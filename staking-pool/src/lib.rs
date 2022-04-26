use std::convert::TryInto;

use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::collections::UnorderedMap;
use near_sdk::json_types::{Base58PublicKey, U128};
use near_sdk::serde::{Deserialize, Serialize};
use near_sdk::{
    env, ext_contract, near_bindgen, AccountId, Balance, EpochHeight, Promise, PromiseResult,
    PublicKey,
};

mod internal;
use internal::math::{Fraction, U256};

/// The amount of gas given to complete `vote` call.
const VOTE_GAS: u64 = 100_000_000_000_000;

/// The amount of gas given to complete internal `on_stake_action` call.
const ON_STAKE_ACTION_GAS: u64 = 20_000_000_000_000;

/// The amount of yocto NEAR the contract dedicates to guarantee that the "share" price never
/// decreases. It's used during rounding errors for share -> amount conversions.
const STAKE_SHARE_PRICE_GUARANTEE_FUND: Balance = 1_000_000_000_000;

/// There is no deposit balance attached.
const NO_DEPOSIT: Balance = 0;

/// A type to distinguish between a balance and "stake" shares for better readability.
pub type NumStakeShares = Balance;

#[cfg(test)]
mod test_utils;

#[global_allocator]
static ALLOC: near_sdk::wee_alloc::WeeAlloc = near_sdk::wee_alloc::WeeAlloc::INIT;

/// Inner account data of a delegate.
#[derive(BorshDeserialize, BorshSerialize, Debug, PartialEq)]
pub struct Account {
    /// The unstaked balance. It represents the amount the account has on this contract that
    /// can either be staked or withdrawn.
    pub unstaked: Balance,
    /// The amount of "stake" shares. Every stake share corresponds to the amount of staked balance.
    /// NOTE: The number of shares should always be less or equal than the amount of staked balance.
    /// This means the price of stake share should always be at least `1`.
    /// The price of stake share can be computed as `total_staked_balance` / `total_stake_shares`.
    pub stake_shares: NumStakeShares,
    /// The minimum epoch height when the withdrawn is allowed.
    /// This changes after unstaking action, because the amount is still locked for 3 epochs.
    pub unstaked_available_epoch_height: EpochHeight,
}

/// Represents an account structure readable by humans.
#[derive(Serialize, Deserialize)]
#[serde(crate = "near_sdk::serde")]
pub struct HumanReadableAccount {
    pub account_id: AccountId,
    /// The unstaked balance that can be withdrawn or staked.
    pub unstaked_balance: U128,
    /// The amount balance staked at the current "stake" share price.
    pub staked_balance: U128,
    /// Whether the unstaked balance is available for withdrawal now.
    pub can_withdraw: bool,
    /// Rewards showing information for those accounts
    /// that have their tokens delegated to a pool which
    /// doesnt restake its rewards
    pub rewards_for_withdraw: U128,
}

impl Default for Account {
    fn default() -> Self {
        Self {
            unstaked: 0,
            stake_shares: 0,
            unstaked_available_epoch_height: 0,
        }
    }
}

/// The number of epochs required for the locked balance to become unlocked.
/// NOTE: The actual number of epochs when the funds are unlocked is 3. But there is a corner case
/// when the unstaking promise can arrive at the next epoch, while the inner state is already
/// updated in the previous epoch. It will not unlock the funds for 4 epochs.
const NUM_EPOCHS_TO_UNLOCK: EpochHeight = 4;

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize)]
pub struct StakingContract {
    /// The account ID of the owner who's running the staking validator node.
    /// NOTE: This is different from the current account ID which is used as a validator account.
    /// The owner of the staking pool can change staking public key and adjust reward fees.
    pub owner_id: AccountId,
    /// The public key which is used for staking action. It's the public key of the validator node
    /// that validates on behalf of the pool.
    pub stake_public_key: PublicKey,
    /// The last epoch height when `ping` was called.
    pub last_epoch_height: EpochHeight,
    /// The last total balance of the account (consists of staked and unstaked balances).
    pub last_total_balance: Balance,
    /// The fraction of the reward that goes to the owner of the staking pool for running the
    /// validator node.
    pub reward_fee_fraction: RewardFeeFraction,
    /// Inner staking pool, that restakes the received rewards
    pub rewards_staked_staking_pool: InnerStakingPool,
    /// Inner staking pool for accounts that provided different delegator address
    pub rewards_not_staked_staking_pool: InnerStakingPoolWithoutRewardsRestaked,
    /// Map showing whether account has his rewards staked or unstaked
    pub account_pool_register: UnorderedMap<AccountId, bool>,
    /// Whether the staking is paused.
    /// When paused, the account unstakes everything (stakes 0) and doesn't restake.
    /// It doesn't affect the staking shares or reward distribution.
    /// Pausing is useful for node maintenance. Only the owner can pause and resume staking.
    /// The contract is not paused by default.
    pub paused: bool,
}

impl Default for StakingContract {
    fn default() -> Self {
        env::panic(b"Staking contract should be initialized before usage")
    }
}

/// Structure containing information for accounts that have their rewards restaked
#[derive(BorshDeserialize, BorshSerialize)]
pub struct InnerStakingPool{
    /// The total amount of shares the staking pool has across the contract
    pub total_stake_shares: NumStakeShares,
    /// The total staked balance.
    pub total_staked_balance: Balance,
    /// Persistent map from an account ID to the corresponding account.
    pub accounts: UnorderedMap<AccountId, Account>,
}

pub trait StakingPool{
    fn get_total_staked_balance(&self) -> Balance;
    fn deposit(&mut self, account_id: &AccountId, amount: Balance);
    fn stake(&mut self, account_id: &AccountId, amount: Balance);
    fn withdraw(&mut self, account_id: &AccountId, amount: Balance) -> bool;
    fn unstake(&mut self, account_id: &AccountId, amount: Balance);
    fn get_account_unstaked_balance(&self, account_id: &AccountId) -> Balance;
    fn get_account_info(&self, account_id: &AccountId) -> HumanReadableAccount;
    /// send rewards to receiver account id
    /// and remove account from account pool register if needed
    /// returns amount to send and flag indicating wether an account should be removed
    /// from register
    fn withdraw_not_staked_rewards(&mut self, account_id: &AccountId) -> (Balance, bool);
}

/// Inner account data of a delegate.
#[derive(BorshDeserialize, BorshSerialize, Debug, PartialEq)]
pub struct AccountWithReward{
    /// The unstaked balance. It represents the amount the account has on this contract that
    /// can either be staked or withdrawn.
    pub unstaked: Balance,
    /// The amount of "stake" shares. Every stake share corresponds to the amount of staked balance.
    /// NOTE: The number of shares should always be less or equal than the amount of staked balance.
    /// This means the price of stake share should always be at least `1`.
    /// The price of stake share can be computed as `total_staked_balance` / `total_stake_shares`.
    pub stake: Balance,
    /// The minimum epoch height when the withdrawn is allowed.
    /// This changes after unstaking action, because the amount is still locked for 3 epochs.
    pub unstaked_available_epoch_height: EpochHeight,
    /// The reward that has been paid to the account
    pub reward_tally: Balance,
    /// Bool variable showing whether the reward_tally is positive or negative
    pub tally_below_zero: bool,
}

impl Default for AccountWithReward {
    fn default() -> Self {
        Self {
            unstaked: 0,
            stake: 0,
            unstaked_available_epoch_height: 0,
            reward_tally: 0,
            tally_below_zero: false,
        }
    }
}

impl AccountWithReward{
    fn add_to_tally(&mut self, amount: Balance){
        if self.tally_below_zero{
            if amount >= self.reward_tally {
                self.reward_tally = amount - self.reward_tally;
                self.tally_below_zero = !self.tally_below_zero; 
            }else{
                self.reward_tally -= amount;
            }
        }else{
            self.reward_tally += amount;
        }
    }

    fn subtract_from_tally(&mut self, amount: Balance){
        if self.tally_below_zero{
            self.reward_tally += amount;            
        }else{
            if amount > self.reward_tally {
                self.reward_tally = amount - self.reward_tally;
                self.tally_below_zero = !self.tally_below_zero; 
            }else{
                self.reward_tally -= amount;
            }
        }
    }
}
/// Structure containing information for accounts that have their rewards not being restaked
#[derive(BorshDeserialize, BorshSerialize)]
pub struct InnerStakingPoolWithoutRewardsRestaked{
    pub accounts: UnorderedMap<AccountId, AccountWithReward>,
    /// Pool total staked balance
    pub total_staked_balance: Balance,
    /// Accounts deposit, it would be used when calculating how much of the total rewards is for each account
    /// and also how much of the total staked balance can be unstaked
    pub reward_per_token: Fraction,
}

#[derive(BorshDeserialize, BorshSerialize, Serialize, Deserialize, Clone)]
#[serde(crate = "near_sdk::serde")]
pub struct RewardFeeFraction {
    pub numerator: u32,
    pub denominator: u32,
}

impl RewardFeeFraction {
    pub fn assert_valid(&self) {
        assert_ne!(self.denominator, 0, "Denominator must be a positive number");
        assert!(
            self.numerator <= self.denominator,
            "The reward fee must be less or equal to 1"
        );
    }

    pub fn multiply(&self, value: Balance) -> Balance {
        (U256::from(self.numerator) * U256::from(value) / U256::from(self.denominator)).as_u128()
    }
}
/// Interface for a voting contract.
#[ext_contract(ext_voting)]
pub trait VoteContract {
    /// Method for validators to vote or withdraw the vote.
    /// Votes for if `is_vote` is true, or withdraws the vote if `is_vote` is false.
    fn vote(&mut self, is_vote: bool);
}

/// Interface for the contract itself.
#[ext_contract(ext_self)]
pub trait SelfContract {
    /// A callback to check the result of the staking action.
    /// In case the stake amount is less than the minimum staking threshold, the staking action
    /// fails, and the stake amount is not changed. This might lead to inconsistent state and the
    /// follow withdraw calls might fail. To mitigate this, the contract will issue a new unstaking
    /// action in case of the failure of the first staking action.
    fn on_stake_action(&mut self);
}

#[near_bindgen]
impl StakingContract {
    /// Initializes the contract with the given owner_id, initial staking public key (with ED25519
    /// curve) and initial reward fee fraction that owner charges for the validation work.
    ///
    /// The entire current balance of this contract will be used to stake. This allows contract to
    /// always maintain staking shares that can't be unstaked or withdrawn.
    /// It prevents inflating the price of the share too much.
    #[init]
    pub fn new(
        owner_id: AccountId,
        stake_public_key: Base58PublicKey,
        reward_fee_fraction: RewardFeeFraction,
    ) -> Self {
        assert!(!env::state_exists(), "Already initialized");
        reward_fee_fraction.assert_valid();
        assert!(
            env::is_valid_account_id(owner_id.as_bytes()),
            "The owner account ID is invalid"
        );
        let account_balance = env::account_balance();
        let total_staked_balance = account_balance - STAKE_SHARE_PRICE_GUARANTEE_FUND;
        assert_eq!(
            env::account_locked_balance(),
            0,
            "The staking pool shouldn't be staking at the initialization"
        );
            
        let mut this = Self {
            owner_id: owner_id.clone(),
            stake_public_key: stake_public_key.into(),
            last_epoch_height: env::epoch_height(),
            last_total_balance: account_balance,
            reward_fee_fraction: reward_fee_fraction,
            rewards_staked_staking_pool: InnerStakingPool::new(
                NumStakeShares::from(total_staked_balance),
                total_staked_balance),
            rewards_not_staked_staking_pool: InnerStakingPoolWithoutRewardsRestaked::new(),
            account_pool_register: UnorderedMap::new(b"a".to_vec()),
            paused: false,
        };
        // save owner account in pool register
        this.internal_register_account_to_staking_pool(&owner_id, true);
        // Staking with the current pool to make sure the staking key is valid.
        this.internal_restake();
        this
    }

    /// Distributes rewards and restakes if needed.
    pub fn ping(&mut self) {
        if self.internal_ping() {
            self.internal_restake();
        }
    }

    /// Deposits the attached amount into the inner account of the predecessor.
    #[payable]
    pub fn deposit(&mut self) {
        let need_to_restake = self.internal_ping();

        self.internal_deposit(true);

        if need_to_restake {
            self.internal_restake();
        }
    }

    #[payable]
    pub fn deposit_rewards_not_stake(&mut self){
        let need_to_restake = self.internal_ping();

        self.internal_deposit(false);

        if need_to_restake {
            self.internal_restake();
        }
    }

    /// Deposits the attached amount into the inner account of the predecessor and stakes it.
    #[payable]
    pub fn deposit_and_stake(&mut self) {
        self.internal_ping();

        let amount = self.internal_deposit(true);
        self.internal_stake(amount);

        self.internal_restake();
    }

    #[payable]
    pub fn deposit_and_stake_rewards_not_stake(&mut self){
        self.internal_ping();

        let amount = self.internal_deposit(false);
        self.internal_stake(amount);

        self.internal_restake();
    }

    /// Withdraws the entire unstaked balance from the predecessor account.
    /// It's only allowed if the `unstake` action was not performed in the four most recent epochs.
    pub fn withdraw_all(&mut self) {
        let need_to_restake = self.internal_ping();

        let account_id = env::predecessor_account_id();
        let amount = self.get_account_unstaked_balance(account_id);
        self.internal_withdraw(amount.0);

        if need_to_restake {
            self.internal_restake();
        }
    }

    /// Withdraws the non staked balance for given account.
    /// It's only allowed if the `unstake` action was not performed in the four most recent epochs.
    pub fn withdraw(&mut self, amount: U128) {
        let need_to_restake = self.internal_ping();

        let amount: Balance = amount.into();
        self.internal_withdraw(amount);

        if need_to_restake {
            self.internal_restake();
        }
    }

    /// Stakes all available unstaked balance from the inner account of the predecessor.
    pub fn stake_all(&mut self) {
        // Stake action always restakes
        self.internal_ping();

        let account_id = env::predecessor_account_id();
        let unstaked_balance = self.get_account_unstaked_balance(account_id);
        self.internal_stake(unstaked_balance.0);

        self.internal_restake();
    }

    /// Stakes the given amount from the inner account of the predecessor.
    /// The inner account should have enough unstaked balance.
    pub fn stake(&mut self, amount: U128) {
        // Stake action always restakes
        self.internal_ping();

        let amount: Balance = amount.into();
        self.internal_stake(amount);

        self.internal_restake();
    }

    /// Unstakes all staked balance from the inner account of the predecessor.
    /// The new total unstaked balance will be available for withdrawal in four epochs.
    pub fn unstake_all(&mut self) {
        // Unstake action always restakes
        self.internal_ping();

        let account_id = env::predecessor_account_id();
        let staked_balance = self.get_account_staked_balance(account_id);
        self.inner_unstake(staked_balance.0);

        self.internal_restake();
    }

    /// Unstakes the given amount from the inner account of the predecessor.
    /// The inner account should have enough staked balance.
    /// The new total unstaked balance will be available for withdrawal in four epochs.
    pub fn unstake(&mut self, amount: U128) {
        // Unstake action always restakes
        self.internal_ping();

        let amount: Balance = amount.into();
        self.inner_unstake(amount);

        self.internal_restake();
    }

    pub fn withdraw_rewards(&mut self, receiver_account_id: AccountId){
        let need_to_restake = self.internal_ping();
        
        self.internal_withdraw_rewards(&receiver_account_id);
        if need_to_restake{
            self.internal_restake();
        }
    }

    /****************/
    /* View methods */
    /****************/

    /// Returns the rewards for the account, If the account is in the
    /// staking pool that doesnt restake its rewards it will return somethind
    /// If is in the other pool it will return 0
    pub fn get_account_not_staked_rewards(&self, account_id: AccountId) -> U128{
        self.get_account(account_id).rewards_for_withdraw
    }

    /// Returns the unstaked balance of the given account.
    pub fn get_account_unstaked_balance(&self, account_id: AccountId) -> U128 {
        self.get_account(account_id).unstaked_balance
    }

    /// Returns the staked balance of the given account.
    /// NOTE: This is computed from the amount of "stake" shares the given account has and the
    /// current amount of total staked balance and total stake shares on the account.
    pub fn get_account_staked_balance(&self, account_id: AccountId) -> U128 {
        self.get_account(account_id).staked_balance
    }

    /// Returns the total balance of the given account (including staked and unstaked balances).
    pub fn get_account_total_balance(&self, account_id: AccountId) -> U128 {
        let account = self.get_account(account_id);
        (account.unstaked_balance.0 + account.staked_balance.0).into()
    }

    /// Returns `true` if the given account can withdraw tokens in the current epoch.
    pub fn is_account_unstaked_balance_available(&self, account_id: AccountId) -> bool {
        self.get_account(account_id).can_withdraw
    }

    /// Returns the total staking balance.
    pub fn get_total_staked_balance(&self) -> U128 {
        (self.rewards_staked_staking_pool.total_staked_balance + self.rewards_not_staked_staking_pool.total_staked_balance)
        .into()
    }

    /// Returns account ID of the staking pool owner.
    pub fn get_owner_id(&self) -> AccountId {
        self.owner_id.clone()
    }

    /// Returns the current reward fee as a fraction.
    pub fn get_reward_fee_fraction(&self) -> RewardFeeFraction {
        self.reward_fee_fraction.clone()
    }

    /// Returns the staking public key
    pub fn get_staking_key(&self) -> Base58PublicKey {
        self.stake_public_key.clone().try_into().unwrap()
    }

    /// Returns true if the staking is paused
    pub fn is_staking_paused(&self) -> bool {
        self.paused
    }

    /// Returns human readable representation of the account for the given account ID.
    pub fn get_account(&self, account_id: AccountId) -> HumanReadableAccount {
        let staking_pool = self.get_staking_pool_or_assert(&account_id);
        return staking_pool.get_account_info(&account_id);
    }

    /// Returns the number of accounts that have positive balance on this staking pool.
    pub fn get_number_of_accounts(&self) -> u64 {
        self.rewards_staked_staking_pool.accounts.len() + self.rewards_not_staked_staking_pool.accounts.len()
    }

    /// Returns the list of accounts
    pub fn get_accounts(&self, from_index: u64, limit: u64) -> Vec<HumanReadableAccount> {
        let keys = self.rewards_staked_staking_pool.accounts.keys_as_vector();

        (from_index..std::cmp::min(from_index + limit, keys.len()))
            .map(|index| self.get_account(keys.get(index).unwrap()))
            .collect()
    }

    /*************/
    /* Callbacks */
    /*************/

    pub fn on_stake_action(&mut self) {
        assert_eq!(
            env::current_account_id(),
            env::predecessor_account_id(),
            "Can be called only as a callback"
        );

        assert_eq!(
            env::promise_results_count(),
            1,
            "Contract expected a result on the callback"
        );
        let stake_action_succeeded = match env::promise_result(0) {
            PromiseResult::Successful(_) => true,
            _ => false,
        };

        // If the stake action failed and the current locked amount is positive, then the contract
        // has to unstake.
        if !stake_action_succeeded && env::account_locked_balance() > 0 {
            Promise::new(env::current_account_id()).stake(0, self.stake_public_key.clone());
        }
    }

    /*******************/
    /* Owner's methods */
    /*******************/

    /// Owner's method.
    /// Updates current public key to the new given public key.
    pub fn update_staking_key(&mut self, stake_public_key: Base58PublicKey) {
        self.assert_owner();
        // When updating the staking key, the contract has to restake.
        let _need_to_restake = self.internal_ping();
        self.stake_public_key = stake_public_key.into();
        self.internal_restake();
    }

    /// Owner's method.
    /// Updates current reward fee fraction to the new given fraction.
    pub fn update_reward_fee_fraction(&mut self, reward_fee_fraction: RewardFeeFraction) {
        self.assert_owner();
        reward_fee_fraction.assert_valid();

        let need_to_restake = self.internal_ping();
        self.reward_fee_fraction = reward_fee_fraction;
        if need_to_restake {
            self.internal_restake();
        }
    }

    /// Owner's method.
    /// Calls `vote(is_vote)` on the given voting contract account ID on behalf of the pool.
    pub fn vote(&mut self, voting_account_id: AccountId, is_vote: bool) -> Promise {
        self.assert_owner();
        assert!(
            env::is_valid_account_id(voting_account_id.as_bytes()),
            "Invalid voting account ID"
        );

        ext_voting::vote(is_vote, &voting_account_id, NO_DEPOSIT, VOTE_GAS)
    }

    /// Owner's method.
    /// Pauses pool staking.
    pub fn pause_staking(&mut self) {
        self.assert_owner();
        assert!(!self.paused, "The staking is already paused");

        self.internal_ping();
        self.paused = true;
        Promise::new(env::current_account_id()).stake(0, self.stake_public_key.clone());
    }

    /// Owner's method.
    /// Resumes pool staking.
    pub fn resume_staking(&mut self) {
        self.assert_owner();
        assert!(self.paused, "The staking is not paused");

        self.internal_ping();
        self.paused = false;
        self.internal_restake();
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use near_sdk::{serde_json, testing_env, MockedBlockchain, VMContext};

    use crate::test_utils::*;

    use super::*;

    struct Emulator {
        pub contract: StakingContract,
        pub epoch_height: EpochHeight,
        pub amount: Balance,
        pub locked_amount: Balance,
        last_total_staked_balance: Balance,
        last_total_stake_shares: Balance,
        context: VMContext,
    }

    fn zero_fee() -> RewardFeeFraction {
        RewardFeeFraction {
            numerator: 0,
            denominator: 1,
        }
    }

    impl Emulator {
        pub fn new(
            owner: String,
            stake_public_key: String,
            reward_fee_fraction: RewardFeeFraction,
            account_balance: Option<Balance>,
        ) -> Self {
            let amount = account_balance.unwrap_or(ntoy(30));
            let context = VMContextBuilder::new()
                .current_account_id(owner.clone())
                .account_balance(amount)
                .finish();
            testing_env!(context.clone());
            let contract = StakingContract::new(
                owner,
                Base58PublicKey::try_from(stake_public_key).unwrap(),
                reward_fee_fraction,
            );
            let last_total_staked_balance = 
                contract.rewards_staked_staking_pool.total_staked_balance
                + contract.rewards_not_staked_staking_pool.total_staked_balance;
            let last_total_stake_shares = contract.rewards_staked_staking_pool.total_stake_shares + contract.rewards_not_staked_staking_pool.total_staked_balance;
            Emulator {
                contract,
                epoch_height: 0,
                amount: amount,
                locked_amount: 0,
                last_total_staked_balance,
                last_total_stake_shares,
                context,
            }
        }

        pub fn deposit(&mut self, amount: Balance){
            self.contract.deposit();
            self.amount += amount;
        }

        fn verify_stake_price_increase_guarantee(&mut self) {
            let total_staked_balance = 
                        self.contract.rewards_staked_staking_pool.total_staked_balance 
                        + self.contract.rewards_not_staked_staking_pool.total_staked_balance;
            let total_stake_shares = self.contract.rewards_staked_staking_pool.total_stake_shares + self.contract.rewards_not_staked_staking_pool.total_staked_balance;
            /*assert!(
                U256::from(total_staked_balance) * U256::from(self.last_total_stake_shares)
                    >= U256::from(self.last_total_staked_balance) * U256::from(total_stake_shares),
                "Price increase guarantee was violated."
            );*/
            self.last_total_staked_balance = total_staked_balance;
            self.last_total_stake_shares = total_stake_shares;
        }

        pub fn update_context(&mut self, predecessor_account_id: String, deposit: Balance) {
            self.verify_stake_price_increase_guarantee();
            self.context = VMContextBuilder::new()
                .current_account_id(staking())
                .predecessor_account_id(predecessor_account_id.clone())
                .signer_account_id(predecessor_account_id)
                .attached_deposit(deposit)
                .account_balance(self.amount)
                .account_locked_balance(self.locked_amount)
                .epoch_height(self.epoch_height)
                .finish();
            testing_env!(self.context.clone());
            println!(
                "Epoch: {}, Deposit: {}, amount: {}, locked_amount: {}",
                self.epoch_height, deposit, self.amount, self.locked_amount
            );
        }

        pub fn simulate_stake_call(&mut self) {
            let mut total_stake = self.contract.rewards_staked_staking_pool.total_staked_balance + self.contract.rewards_not_staked_staking_pool.total_staked_balance;
            let mut saved_rewards = 0u128;

            for acc 
                in self.contract.rewards_not_staked_staking_pool.accounts.values_as_vector().iter() {
                saved_rewards += self.contract.rewards_not_staked_staking_pool.compute_reward(&acc);
            }
            total_stake += saved_rewards;
            // Stake action
            self.amount = self.amount + self.locked_amount - total_stake;
            self.locked_amount = total_stake;
            // Second function call action
            self.update_context(staking(), 0);
        }

        pub fn skip_epochs(&mut self, num: EpochHeight) {
            self.epoch_height += num;
            self.locked_amount = (self.locked_amount * (100 + u128::from(num))) / 100;
        }
    }

    #[test]
    fn test_restake_fail() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        emulator.update_context(bob(), 0);
        emulator.contract.internal_restake();
        let receipts = env::created_receipts();
        assert_eq!(receipts.len(), 2);
        // Mocked Receipt fields are private, so can't check directly.
        assert!(serde_json::to_string(&receipts[0])
            .unwrap()
            .contains("\"actions\":[{\"Stake\":{\"stake\":29999999999999000000000000,"));
        assert!(serde_json::to_string(&receipts[1])
            .unwrap()
            .contains("\"method_name\":\"on_stake_action\""));
        emulator.simulate_stake_call();

        emulator.update_context(staking(), 0);
        testing_env_with_promise_results(emulator.context.clone(), PromiseResult::Failed);
        emulator.contract.on_stake_action();
        let receipts = env::created_receipts();
        assert_eq!(receipts.len(), 1);
        assert!(serde_json::to_string(&receipts[0])
            .unwrap()
            .contains("\"actions\":[{\"Stake\":{\"stake\":0,"));
    }

    #[test]
    #[should_panic(expected = "Account should be registered for one of the staking pools")]
    fn test_deposit_withdraw() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        let deposit_amount = ntoy(1_000_000);
        emulator.update_context(bob(), deposit_amount);
        emulator.contract.deposit();
        emulator.amount += deposit_amount;
        emulator.update_context(bob(), 0);
        assert_eq!(
            emulator.contract.get_account_unstaked_balance(bob()).0,
            deposit_amount
        );
        emulator.contract.withdraw(deposit_amount.into());
        assert_eq!(
            emulator.contract.get_account_unstaked_balance(bob()).0,
            0u128
        );
    }

    #[test]
    fn test_stake_with_fee() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            RewardFeeFraction {
                numerator: 10,
                denominator: 100,
            },
            None,
        );
        let deposit_amount = ntoy(1_000_000);
        emulator.update_context(bob(), deposit_amount);
        emulator.contract.deposit();
        emulator.amount += deposit_amount;
        emulator.update_context(bob(), 0);
        emulator.contract.stake(deposit_amount.into());
        emulator.simulate_stake_call();
        assert_eq!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount
        );

        let locked_amount = emulator.locked_amount;
        let n_locked_amount = yton(locked_amount);
        emulator.skip_epochs(10);
        // Overriding rewards (+ 100K reward)
        emulator.locked_amount = locked_amount + ntoy(100_000);
        emulator.update_context(bob(), 0);    
        emulator.contract.ping();
        let expected_amount = deposit_amount
            + ntoy((yton(deposit_amount) * 90_000 + n_locked_amount / 2) / n_locked_amount);
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            expected_amount
        );
        // Owner got 10% of the rewards
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(owner()).0,
            ntoy(10_000)
        );

        let locked_amount = emulator.locked_amount;
        let n_locked_amount = yton(locked_amount);
        emulator.skip_epochs(10);
        // Overriding rewards (another 100K reward)
        emulator.locked_amount = locked_amount + ntoy(100_000);
        
        emulator.update_context(bob(), 0);
        emulator.contract.ping();
        // previous balance plus (1_090_000 / 1_100_030)% of the 90_000 reward (rounding to nearest).
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            expected_amount
                + ntoy((yton(expected_amount) * 90_000 + n_locked_amount / 2) / n_locked_amount)
        );
        // owner earns 10% with the fee and also small percentage from restaking.
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(owner()).0,
            ntoy(10_000)
                + ntoy(10_000)
                + ntoy((10_000u128 * 90_000 + n_locked_amount / 2) / n_locked_amount)
        );

        assert_eq!(emulator.contract.get_number_of_accounts(), 2);
    }

    #[test]
    fn test_stake_unstake() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        let deposit_amount = ntoy(1_000_000);
        emulator.update_context(bob(), deposit_amount);
        emulator.contract.deposit();
        emulator.amount += deposit_amount;
        emulator.update_context(bob(), 0);
        emulator.contract.stake(deposit_amount.into());
        emulator.simulate_stake_call();
        assert_eq!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount
        );
        let locked_amount = emulator.locked_amount;
        // 10 epochs later, unstake half of the money.
        emulator.skip_epochs(10);
        // Overriding rewards
        emulator.locked_amount = locked_amount + ntoy(10);
        emulator.update_context(bob(), 0);
        emulator.contract.ping();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount + ntoy(10)
        );
        emulator.contract.unstake((deposit_amount / 2).into());
        emulator.simulate_stake_call();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount / 2 + ntoy(10)
        );
        assert_eq_in_near!(
            emulator.contract.get_account_unstaked_balance(bob()).0,
            deposit_amount / 2
        );
        let acc = emulator.contract.get_account(bob());
        assert_eq!(acc.account_id, bob());
        assert_eq_in_near!(acc.unstaked_balance.0, deposit_amount / 2);
        assert_eq_in_near!(acc.staked_balance.0, deposit_amount / 2 + ntoy(10));
        assert!(!acc.can_withdraw);

        assert!(!emulator
            .contract
            .is_account_unstaked_balance_available(bob()),);
        emulator.skip_epochs(4);
        emulator.update_context(bob(), 0);
        assert!(emulator
            .contract
            .is_account_unstaked_balance_available(bob()),);
    }

    #[test]
    fn test_stake_all_unstake_all() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        let deposit_amount = ntoy(1_000_000);
        emulator.update_context(bob(), deposit_amount);
        emulator.contract.deposit_and_stake();
        emulator.amount += deposit_amount;
        emulator.simulate_stake_call();
        assert_eq!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount
        );
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(bob()).0, 0);
        let locked_amount = emulator.locked_amount;

        // 10 epochs later, unstake all.
        emulator.skip_epochs(10);
        // Overriding rewards
        emulator.locked_amount = locked_amount + ntoy(10);
        emulator.update_context(bob(), 0);
        emulator.contract.ping();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            deposit_amount + ntoy(10)
        );
        emulator.contract.unstake_all();
        emulator.simulate_stake_call();
        assert_eq_in_near!(emulator.contract.get_account_staked_balance(bob()).0, 0);
        assert_eq_in_near!(
            emulator.contract.get_account_unstaked_balance(bob()).0,
            deposit_amount + ntoy(10)
        );
    }

    /// Test that two can delegate and then undelegate their funds and rewards at different time.
    #[test]
    fn test_two_delegates() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        emulator.update_context(alice(), ntoy(1_000_000));
        emulator.contract.deposit();
        emulator.amount += ntoy(1_000_000);
        emulator.update_context(alice(), 0);
        emulator.contract.stake(ntoy(1_000_000).into());
        emulator.simulate_stake_call();
        emulator.skip_epochs(3);
        emulator.update_context(bob(), ntoy(1_000_000));

        emulator.contract.deposit();
        emulator.amount += ntoy(1_000_000);
        emulator.update_context(bob(), 0);
        emulator.contract.stake(ntoy(1_000_000).into());
        emulator.simulate_stake_call();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            ntoy(1_000_000)
        );
        emulator.skip_epochs(3);
        emulator.update_context(alice(), 0);
        emulator.contract.ping();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(alice()).0,
            ntoy(1_060_900) - 1
        );
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            ntoy(1_030_000)
        );

        // Checking accounts view methods
        // Should be 2, because the pool has 0 fee.
        assert_eq!(emulator.contract.get_number_of_accounts(), 2);
        let accounts = emulator.contract.get_accounts(0, 10);
        assert_eq!(accounts.len(), 2);
        assert_eq!(accounts[0].account_id, alice());
        assert_eq!(accounts[1].account_id, bob());

        let accounts = emulator.contract.get_accounts(1, 10);
        assert_eq!(accounts.len(), 1);
        assert_eq!(accounts[0].account_id, bob());

        let accounts = emulator.contract.get_accounts(0, 1);
        assert_eq!(accounts.len(), 1);
        assert_eq!(accounts[0].account_id, alice());

        let accounts = emulator.contract.get_accounts(2, 10);
        assert_eq!(accounts.len(), 0);
    }

    #[test]
    fn test_low_balances() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        let initial_balance = 100;
        emulator.update_context(alice(), initial_balance);
        emulator.contract.deposit();
        emulator.amount += initial_balance;
        let mut remaining = initial_balance;
        let mut amount = 1;
        while remaining >= 4 {
            emulator.update_context(alice(), 0);
            amount = 2 + (amount - 1) % 3;
            emulator.contract.stake(amount.into());
            emulator.simulate_stake_call();
            remaining -= amount;
        }
    }

    #[test]
    fn test_rewards() {
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            None,
        );
        let initial_balance = ntoy(100);
        emulator.update_context(alice(), initial_balance);
        emulator.contract.deposit();
        emulator.amount += initial_balance;
        let mut remaining = 100;
        let mut amount = 1;
        while remaining >= 4 {
            emulator.skip_epochs(3);
            emulator.update_context(alice(), 0);
            emulator.contract.ping();
            emulator.update_context(alice(), 0);
            amount = 2 + (amount - 1) % 3;
            emulator.contract.stake(ntoy(amount).into());
            emulator.simulate_stake_call();
            remaining -= amount;
        }
    }

    #[test]
    fn test_fraction(){
        let f = Fraction::new(17, 32);

        assert_eq!(f.multiply(43), 22);
        assert_eq_in_near!(ntoy(50), Fraction::new(1, 2).multiply(ntoy(100)));
        assert_eq!(*Fraction::new(3, 5).add(Fraction::new(3, 11)), Fraction::new(48, 55));

        let mut f1 = Fraction::new(1, 3);
        let f2 = Fraction::new(3, 5);
        f1.add(f2);
        assert_eq!(f1, Fraction::new(14,15));
        assert_eq_in_near!(f1.multiply(ntoy(30)), ntoy(28));

        assert_eq!(0, Fraction::new(1, 5).add(Fraction::new(1,5)).multiply(0));
        assert_eq!(Fraction::new(0, 0).add(Fraction::new(1,5)), &Fraction::new(1,5));
        assert_eq!(Fraction::new(1,5).add(Fraction::default()), &Fraction::new(1,5));
        assert_eq!(Fraction::new(0,0).add(Fraction::default()), &Fraction::default());
    }

    #[test]
    fn test_two_staking_pools_total_balance(){
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            Some(ntoy(110)),
        );

        let bob_deposit_amount = ntoy(50);
        emulator.update_context(bob(), bob_deposit_amount);
        emulator.deposit(bob_deposit_amount);
        emulator.contract.stake(bob_deposit_amount.into());
        emulator.simulate_stake_call();
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(bob()).0,
            bob_deposit_amount
        );
        assert_eq_in_near!(
            emulator.contract.get_total_staked_balance().0,
            emulator.contract.rewards_staked_staking_pool.total_staked_balance
        );
        
        let alice_deposit = ntoy(100);
        let alice_stake = alice_deposit * 5 / 10;
        emulator.update_context(alice(), alice_deposit);
        emulator.contract.deposit_rewards_not_stake();
        emulator.amount += alice_deposit;
        emulator.contract.stake(alice_stake.into());
        emulator.simulate_stake_call();

        assert_eq_in_near!(
            emulator.contract.get_total_staked_balance().0,
            emulator.contract.rewards_staked_staking_pool.total_staked_balance +
            emulator.contract.rewards_not_staked_staking_pool.total_staked_balance
        );
        assert_eq_in_near!(
            emulator.contract.get_account_staked_balance(alice()).0,
            emulator.contract.rewards_not_staked_staking_pool.total_staked_balance
        );
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(bob()).0, 0);
        let locked_amount = emulator.locked_amount;

        // 10 epochs later, unstake all.
        emulator.skip_epochs(10);
        let rewards = ntoy(10u128);
        // Overriding rewards
        emulator.locked_amount = locked_amount + rewards;
        // Compare total staked balance, before reward and after it
        // it should be increased by rewards variable without the rewards of the accounts
        // that are in the pool which doesnt restakes them, in this situation there is only 1 such account
        let mut total_staked_balance = emulator.contract.get_total_staked_balance().0;
        emulator.update_context(bob(), 0);
        emulator.contract.ping();
        assert_eq_in_near!(emulator.contract.get_total_staked_balance().0, 
        total_staked_balance + rewards  - emulator.contract.get_account_not_staked_rewards(alice()).0);
        
        total_staked_balance = emulator.contract.get_total_staked_balance().0;
        emulator.update_context(alice(), 0);
        emulator.contract.unstake_all();

        assert_eq_in_near!(emulator.contract.get_total_staked_balance().0, total_staked_balance - alice_stake);
    }

    #[test]
    fn test_check_rewards(){
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            Some(ntoy(110)),
        );

        let bob_deposit_amount = ntoy(100);
        emulator.update_context(bob(), bob_deposit_amount);
        emulator.contract.deposit_rewards_not_stake();
        emulator.amount+=bob_deposit_amount;
        emulator.contract.stake(bob_deposit_amount.into());
        emulator.simulate_stake_call();

        let locked_amount = emulator.locked_amount;

        // 10 epochs later, unstake all.
        emulator.skip_epochs(10);
        let rewards = ntoy(10u128);
        // Overriding rewards
        emulator.locked_amount = locked_amount + rewards;
        emulator.update_context(alice(), 0);
        emulator.contract.ping();
        emulator.update_context(bob(), 0);
        println!("{}", yton(rewards*5/10));
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(bob()).0, rewards * 5 / 10);
        assert_eq_in_near!(emulator.contract.get_account_staked_balance(bob()).0, bob_deposit_amount);
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(bob()).0, 0);
        
        emulator.contract.unstake_all();
        emulator.simulate_stake_call();
        assert_eq_in_near!(emulator.contract.get_account_staked_balance(bob()).0, 0);
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(bob()).0, bob_deposit_amount);
        emulator.skip_epochs(5);
        emulator.update_context(bob(), 0);
        emulator.contract.withdraw_all();
        println!("Bob rewards {}, rewards in near {}", emulator.contract.get_account_not_staked_rewards(bob()).0,
    yton(emulator.contract.get_account_not_staked_rewards(bob()). 0));
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(bob()).0, rewards * 5 / 10);
        assert_eq_in_near!(emulator.contract.get_account_staked_balance(bob()).0, 0);
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(bob()).0, 0);
    }

    #[test]
    fn test_stake_two_pools(){
        let initial_balance = ntoy(100);
        let mut emulator = Emulator::new(
            owner(),
            "KuTCtARNzxZQ3YvXDeLjx83FDqxv2SdQTSbiq876zR7".to_string(),
            zero_fee(),
            Some(initial_balance),
        );
        // 5 delegators A, B, C, D, E
        // A, B -> first pool that stakes rewards (50, 100 (stakes 50))
        // C, E -> second pool that saves the rewards (60, 40)
        // D -> comes after first iteration of rewards is distributes in the second pool (100)
        
        let a_deposit_amount = ntoy(50);
        let b_deposit_amount = ntoy(100);
        let c_deposit_amount = ntoy(60);
        let e_deposit_amount = ntoy(40);
        let d_deposit_amount = ntoy(100);
        // A deposits and stakes all
        emulator.update_context(A(), a_deposit_amount);
        emulator.contract.deposit();
        emulator.amount += a_deposit_amount;
        emulator.contract.stake_all();
        emulator.simulate_stake_call();

        // B deposits and stakes 50/100
        emulator.update_context(B(), b_deposit_amount);
        emulator.contract.deposit();
        emulator.amount += b_deposit_amount;
        let b_stake_amount = b_deposit_amount * 5 / 10;
        emulator.contract.stake((b_stake_amount).into());
        emulator.simulate_stake_call();

        // C deposits and stakes all
        emulator.update_context(C(), c_deposit_amount);
        emulator.contract.deposit_and_stake_rewards_not_stake();
        emulator.amount += c_deposit_amount;
        emulator.simulate_stake_call();

        // E deposits and stakes all
        emulator.update_context(E(), e_deposit_amount);
        emulator.contract.deposit_rewards_not_stake();
        emulator.amount += e_deposit_amount;
        emulator.contract.stake_all();
        emulator.simulate_stake_call();

        let mut locked_amount = emulator.locked_amount;
        emulator.skip_epochs(5);

        // override rewards
        let mut rewards = ntoy(60);
        emulator.locked_amount = locked_amount + rewards;
        emulator.update_context(A(), 0);
        let mut expected_reward = emulator.locked_amount + emulator.amount - emulator.contract.last_total_balance;
        assert_eq!(rewards, expected_reward);
        emulator.contract.ping();
        emulator.update_context(A(), 0);
        assert_eq_in_near!(emulator.contract.rewards_staked_staking_pool.total_staked_balance, 
            a_deposit_amount + b_stake_amount + ntoy(40) + initial_balance);

        assert_eq_in_near!(emulator.contract.rewards_not_staked_staking_pool.total_staked_balance,
            c_deposit_amount + e_deposit_amount);

        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(C()).0, ntoy(12));
        //emulator.simulate_stake_call();

        // D deposit and stake
        emulator.update_context(D(), d_deposit_amount);
        emulator.contract.deposit_rewards_not_stake();
        emulator.amount += d_deposit_amount;
        emulator.contract.stake_all();
        emulator.simulate_stake_call();

        locked_amount = emulator.locked_amount;
        emulator.skip_epochs(5);
        rewards = ntoy(132);
        emulator.locked_amount = locked_amount + rewards;
        emulator.update_context(A(), 0);
        expected_reward = emulator.locked_amount + emulator.amount - emulator.contract.last_total_balance;
        assert_eq!(rewards, expected_reward);
        emulator.contract.ping();

        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(D()).0, ntoy(30));
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(E()).0, ntoy(8) + ntoy(12));
        println!("Total staked balance for first pool {}", emulator.contract.rewards_staked_staking_pool.total_staked_balance);

        emulator.update_context(E(), 0);
        let e_rewards = emulator.contract.get_account_not_staked_rewards(E()).0;
        emulator.contract.withdraw_rewards(bob());
        emulator.locked_amount -= e_rewards;

        assert_eq!(emulator.contract.get_account_not_staked_rewards(E()).0, 0);
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(D()).0, ntoy(30));

        emulator.update_context(B(), 0);
        assert_eq_in_near!(emulator.contract.get_account_staked_balance(B()).0, b_stake_amount + ntoy(10 + 18));
        println!("Total staked balance before B exit {}", yton(emulator.contract.rewards_staked_staking_pool.total_staked_balance));
        emulator.contract.unstake_all();
        emulator.simulate_stake_call();
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(B()).0, b_deposit_amount + ntoy(10) + ntoy(18));
        assert_eq!(emulator.contract.get_account_staked_balance(B()).0, 0);
        println!("Total staked balance for first pool {}", yton(emulator.contract.rewards_staked_staking_pool.total_staked_balance));

        // Overriding rewards
        locked_amount = emulator.locked_amount;
        emulator.skip_epochs(5);
        rewards = ntoy(434);
        emulator.locked_amount = locked_amount + rewards;
        emulator.update_context(B(), 0);
        assert_eq_in_near!(emulator.contract.rewards_staked_staking_pool.total_stake_shares, ntoy(100 + 50));
        assert_eq_in_near!(emulator.contract.rewards_not_staked_staking_pool.total_staked_balance, ntoy(60 + 40 + 100));
        println!("first pool total staked {}", yton(emulator.contract.rewards_staked_staking_pool.total_staked_balance));
        
        expected_reward = emulator.locked_amount + emulator.amount - emulator.contract.last_total_balance;
        assert_eq!(rewards, expected_reward);

        emulator.contract.ping();
        let b_withdraw_amount = emulator.contract.get_account_unstaked_balance(B()).0;
        emulator.contract.withdraw_all();
        emulator.amount -= b_withdraw_amount;

        emulator.update_context(E(), 0);
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(D()).0, ntoy(30 + 100));
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(E()).0, ntoy(40));
        emulator.contract.unstake_all();
        emulator.simulate_stake_call();
        assert_eq_in_near!(emulator.contract.rewards_not_staked_staking_pool.total_staked_balance, ntoy(60 + 100));
        assert_eq_in_near!(emulator.contract.rewards_staked_staking_pool.total_staked_balance, ntoy(234+234));
        
        locked_amount = emulator.locked_amount;
        emulator.skip_epochs(5);
        rewards = ntoy(628);
        emulator.locked_amount = locked_amount + rewards;
        expected_reward = emulator.locked_amount + emulator.amount - emulator.contract.last_total_balance;
        assert_eq!(rewards, expected_reward);

        emulator.contract.ping();
        emulator.update_context(E(), 0);

        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(E()).0, ntoy(40));
        assert_eq_in_near!(emulator.contract.get_account_unstaked_balance(E()).0, e_deposit_amount);
        assert_eq!(emulator.contract.get_account_staked_balance(E()).0, 0);

        emulator.contract.withdraw_all();
        emulator.update_context(E(), 0);
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(E()).0, ntoy(40));
        emulator.contract.withdraw_rewards(bob());
        emulator.update_context(D(), 0);
        assert_eq_in_near!(emulator.contract.get_account_not_staked_rewards(D()).0, ntoy(30 + 100 + 100));
    }
}
