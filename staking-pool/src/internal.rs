use crate::*;

impl StakingContract {
    /********************/
    /* Internal methods */
    /********************/

    /// Restakes the current `total_staked_balance` again.
    pub(crate) fn internal_restake(&mut self) {
        if self.paused {
            return;
        }
        // Stakes with the staking public key. If the public key is invalid the entire function
        // call will be rolled back.
        Promise::new(env::current_account_id())
            .stake(self.rewards_staked_staking_pool.get_total_staked_balance() 
                + self.rewards_not_staked_staking_pool.get_total_staked_balance(), self.stake_public_key.clone())
            .then(ext_self::on_stake_action(
                &env::current_account_id(),
                NO_DEPOSIT,
                ON_STAKE_ACTION_GAS,
            ));
    }

    pub(crate) fn internal_deposit(&mut self, should_staking_pool_restake_rewards: bool) -> u128 {
        let account_id = env::predecessor_account_id();
        let staking_pool = self.get_staking_pool_or_create(&account_id, should_staking_pool_restake_rewards);
        let amount = env::attached_deposit();

        staking_pool.deposit(&account_id, amount);
        self.last_total_balance += amount;

        amount
    }

    pub(crate) fn internal_withdraw_rewards(&mut self, receiver_account_id: &AccountId){
        assert!(
            env::is_valid_account_id(receiver_account_id.as_bytes()),
            "The receiver account ID is invalid"
        );
        let account_id = env::predecessor_account_id();
        let staking_pool = self.get_staking_pool_or_assert_if_not_present(&account_id);
        let (reward, account_should_be_removed) = staking_pool.withdraw_not_staked_rewards(&account_id);
        if account_should_be_removed {
            self.account_pool_register.remove(&account_id);
        }

        if reward != 0 {
            Promise::new(receiver_account_id.to_string()).transfer(reward);
            self.last_total_balance -= reward;
        }
    }

    pub(crate) fn internal_withdraw(&mut self, amount: Balance) {
        assert!(amount > 0, "Withdrawal amount should be positive");

        let account_id = env::predecessor_account_id();
        let staking_pool = self.get_staking_pool_or_assert_if_not_present(&account_id);
        let should_remove_account_from_staking_pool_register = staking_pool.withdraw(&account_id, amount);

        if should_remove_account_from_staking_pool_register{
            self.account_pool_register.remove(&account_id);
        }

        Promise::new(account_id).transfer(amount);
        self.last_total_balance -= amount;
    }

    pub(crate) fn internal_stake(&mut self, amount: Balance) {
        assert!(amount > 0, "Staking amount should be positive");

        let account_id = env::predecessor_account_id();
        let staking_pool = self.get_staking_pool_or_assert_if_not_present(&account_id);
        staking_pool.stake(&account_id, amount);
    }

    pub(crate) fn inner_unstake(&mut self, amount: u128) {
        assert!(amount > 0, "Unstaking amount should be positive");

        let account_id = env::predecessor_account_id();
        let staking_pool = self.get_staking_pool_or_assert_if_not_present(&account_id);
        staking_pool.unstake(&account_id, amount);
    }

    /// Asserts that the method was called by the owner.
    pub(crate) fn assert_owner(&self) {
        assert_eq!(
            env::predecessor_account_id(),
            self.owner_id,
            "Can only be called by the owner"
        );
    }

    /// Distributes rewards after the new epoch. It's automatically called before every action.
    /// Returns true if the current epoch height is different from the last epoch height.
    pub(crate) fn internal_ping(&mut self) -> bool {
        let epoch_height = env::epoch_height();
        if self.last_epoch_height == epoch_height {
            return false;
        }
        self.last_epoch_height = epoch_height;

        // New total amount (both locked and unlocked balances).
        // NOTE: We need to subtract `attached_deposit` in case `ping` called from `deposit` call
        // since the attached deposit gets included in the `account_balance`, and we have not
        // accounted it yet.
        let total_balance =
            env::account_locked_balance() + env::account_balance() - env::attached_deposit();

        assert!(
            total_balance >= self.last_total_balance,
            "The new total balance should not be less than the old total balance"
        );
        let total_reward = total_balance - self.last_total_balance;
        if total_reward > 0 {
            // The validation fee that the contract owner takes.
            let owners_fee = self.reward_fee_fraction.multiply(total_reward);

            // Distributing the remaining reward to the delegators first.
            let remaining_reward = total_reward - owners_fee;
            // Distribute remaining reward between the two pools
            let not_staked_rewards = self.part_of_amount_based_on_stake_share_rounded_down(
                remaining_reward, 
                self.rewards_not_staked_staking_pool.total_staked_balance);

            self.rewards_not_staked_staking_pool.distribute_reward(not_staked_rewards);
            self.rewards_staked_staking_pool.total_staked_balance += remaining_reward - not_staked_rewards;
            
            // Now buying "stake" shares for the contract owner at the new share price.
            let num_shares = self.rewards_staked_staking_pool.num_shares_from_staked_amount_rounded_down(owners_fee);
            if num_shares > 0 {
                // Updating owner's inner account
                let owner_id = self.owner_id.clone();
                let mut account = self.rewards_staked_staking_pool.internal_get_account(&owner_id);
                account.stake_shares += num_shares;
                self.rewards_staked_staking_pool.internal_save_account(&owner_id, &account);
                // Increasing the total amount of "stake" shares.
                self.rewards_staked_staking_pool.total_stake_shares += num_shares;
            }
            // Increasing the total staked balance by the owners fee, no matter whether the owner
            // received any shares or not.
            self.rewards_staked_staking_pool.total_staked_balance += owners_fee;

            env::log(
                format!(
                    "Epoch {}: Contract received total rewards of {} tokens. New total staked balance is {}. Total number of shares {}",
                    epoch_height, total_reward, self.rewards_staked_staking_pool.total_staked_balance, self.rewards_staked_staking_pool.total_stake_shares,
                )
                    .as_bytes(),
            );
            if num_shares > 0 {
                env::log(format!("Total rewards fee is {} stake shares.", num_shares).as_bytes());
            }
        }

        self.last_total_balance = total_balance;
        true
    }

    fn part_of_amount_based_on_stake_share_rounded_down(&self, amount: Balance, stake:Balance) -> Balance{
        (U256::from(stake) * U256::from(amount)
            / (U256::from(self.rewards_staked_staking_pool.total_staked_balance) 
            + U256::from(self.rewards_not_staked_staking_pool.total_staked_balance)))
        .as_u128()
    }

    /// Register account to which staking pool it belongs
    pub(crate) fn internal_register_account_to_staking_pool(&mut self, account_id: &AccountId, do_stake_rewards: bool){
        self.account_pool_register.insert(account_id, &do_stake_rewards);
    }

    /// Get staking pool for account id, if its not present create it
    /// based on client intention, if he wants his rewards to be restaked or not
    pub(crate) fn get_staking_pool_or_create(&mut self, account_id: &AccountId, should_staking_pool_restake_rewards: bool) -> &mut dyn StakingPool{
        let account_staking_pool_option = self.account_pool_register.get(&account_id);

        if account_staking_pool_option.is_none(){
            self.internal_register_account_to_staking_pool(account_id, should_staking_pool_restake_rewards);
        }

        if account_staking_pool_option.unwrap_or(should_staking_pool_restake_rewards) {
            return &mut self.rewards_staked_staking_pool;
        }else{
            return &mut self.rewards_not_staked_staking_pool;
        }
    }

    /// Get staking pool for account id, if not present throw an error
    pub(crate) fn get_staking_pool_or_assert_if_not_present(&mut self, account_id: &AccountId) -> &mut dyn StakingPool{
        let account_staking_pool_option = self.account_pool_register.get(&account_id);
        assert!(account_staking_pool_option.is_some(), "Account should be registered for one of the staking pools");

        if account_staking_pool_option.unwrap() {
            return &mut self.rewards_staked_staking_pool;
        }else{
            return &mut self.rewards_not_staked_staking_pool;
        }
    }

    pub(crate) fn get_staking_pool_or_assert(&self, account_id: &AccountId) -> &dyn StakingPool{
        let account_staking_pool_option = self.account_pool_register.get(&account_id);
        assert!(account_staking_pool_option.is_some(), "Account should be registered for one of the staking pools");

        if account_staking_pool_option.unwrap() {
            return &self.rewards_staked_staking_pool;
        }else{
            return &self.rewards_not_staked_staking_pool;
        }
    }
}

impl InnerStakingPool{

    /// Constructor
    pub fn new(
        stake_shares: NumStakeShares,
        staked_balance: Balance
    ) -> Self{
        let this = Self{
            accounts: UnorderedMap::new(b"u".to_vec()),
            total_stake_shares: stake_shares,
            total_staked_balance: staked_balance
        };

        return this;
    }

    /// Calculate stake shares in the internal staking pool
    /// Returns the number of "stake" shares rounded down corresponding to the given staked balance
    /// amount.
    ///
    /// price = total_staked / total_shares
    /// Price is fixed
    /// (total_staked + amount) / (total_shares + num_shares) = total_staked / total_shares
    /// (total_staked + amount) * total_shares = total_staked * (total_shares + num_shares)
    /// amount * total_shares = total_staked * num_shares
    /// num_shares = amount * total_shares / total_staked
    pub(crate) fn num_shares_from_staked_amount_rounded_down(
        &self,
        amount: Balance,
    ) -> NumStakeShares {
        assert!(
            self.total_staked_balance > 0,
            "The total staked balance can't be 0"
        );
        (U256::from(self.total_stake_shares) * U256::from(amount)
            / U256::from(self.total_staked_balance))
        .as_u128()
    }

    /// Returns the staked amount rounded down corresponding to the given number of "stake" shares.
    pub(crate) fn staked_amount_from_num_shares_rounded_down(
        &self,
        num_shares: NumStakeShares,
    ) -> Balance {
        assert!(
            self.total_stake_shares > 0,
            "The total number of stake shares can't be 0"
        );
        (U256::from(self.total_staked_balance) * U256::from(num_shares)
            / U256::from(self.total_stake_shares))
        .as_u128()
    }

    /// Returns the number of "stake" shares rounded up corresponding to the given staked balance
    /// amount.
    ///
    /// Rounding up division of `a / b` is done using `(a + b - 1) / b`.
    pub(crate) fn num_shares_from_staked_amount_rounded_up(
        &self,
        amount: Balance,
    ) -> NumStakeShares {
        assert!(
            self.total_staked_balance > 0,
            "The total staked balance can't be 0"
        );
        ((U256::from(self.total_stake_shares) * U256::from(amount)
            + U256::from(self.total_staked_balance - 1))
            / U256::from(self.total_staked_balance))
        .as_u128()
    }

    /// Returns the staked amount rounded up corresponding to the given number of "stake" shares.
    ///
    /// Rounding up division of `a / b` is done using `(a + b - 1) / b`.
    pub(crate) fn staked_amount_from_num_shares_rounded_up(
        &self,
        num_shares: NumStakeShares,
    ) -> Balance {
        assert!(
            self.total_stake_shares > 0,
            "The total number of stake shares can't be 0"
        );
        ((U256::from(self.total_staked_balance) * U256::from(num_shares)
            + U256::from(self.total_stake_shares - 1))
            / U256::from(self.total_stake_shares))
        .as_u128()
    }

    /// Inner method to get the given account or a new default value account.
    pub(crate) fn internal_get_account(&self, account_id: &AccountId) -> Account {
        self.accounts.get(account_id).unwrap_or_default()
    }

    /// Inner method to save the given account for a given account ID.
    /// If the account balances are 0, the account is deleted instead to release storage.
    /// Returns true or false, wether an element has been removed
    pub(crate) fn internal_save_account(&mut self, account_id: &AccountId, account: &Account) -> bool{
        if account.unstaked > 0 || account.stake_shares > 0 {
            self.accounts.insert(account_id, &account);
            return false;
        } else {
            self.accounts.remove(account_id);
            return true;
        }
    }
}


impl StakingPool for InnerStakingPool{
    fn get_total_staked_balance(&self) -> Balance{
        return self.total_staked_balance;
    }

    fn stake(&mut self, account_id: &AccountId, amount: Balance){
        assert!(amount > 0, "Staking amount should be positive");

        let mut account = self.internal_get_account(&account_id);

        // Calculate the number of "stake" shares that the account will receive for staking the
        // given amount.
        let num_shares = self.num_shares_from_staked_amount_rounded_down(amount);
        assert!(
            num_shares > 0,
            "The calculated number of \"stake\" shares received for staking should be positive"
        );
        // The amount of tokens the account will be charged from the unstaked balance.
        // Rounded down to avoid overcharging the account to guarantee that the account can always
        // unstake at least the same amount as staked.
        let charge_amount = self.staked_amount_from_num_shares_rounded_down(num_shares);
        assert!(
            charge_amount > 0,
            "Invariant violation. Calculated staked amount must be positive, because \"stake\" share price should be at least 1"
        );

        assert!(
            account.unstaked >= charge_amount,
            "Not enough unstaked balance to stake"
        );
        account.unstaked -= charge_amount;
        account.stake_shares += num_shares;
        self.internal_save_account(&account_id, &account);

        // The staked amount that will be added to the total to guarantee the "stake" share price
        // never decreases. The difference between `stake_amount` and `charge_amount` is paid
        // from the allocated STAKE_SHARE_PRICE_GUARANTEE_FUND.
        let stake_amount = self.staked_amount_from_num_shares_rounded_up(num_shares);

        self.total_staked_balance += stake_amount;
        self.total_stake_shares += num_shares;

        env::log(
            format!(
                "@{} staking {}. Received {} new staking shares. Total {} unstaked balance and {} staking shares",
                account_id, charge_amount, num_shares, account.unstaked, account.stake_shares
            )
                .as_bytes(),
        );
        env::log(
            format!(
                "Contract total staked balance is {}. Total number of shares {}",
                self.total_staked_balance, self.total_stake_shares
            )
            .as_bytes(),
        );
    }

    fn deposit(&mut self, account_id: &AccountId, amount: Balance){
        let mut account = self.internal_get_account(&account_id);
        
        account.unstaked += amount;
        self.internal_save_account(&account_id, &account);

        env::log(
            format!(
                "@{} deposited {}. New unstaked balance is {}",
                account_id, amount, account.unstaked
            )
            .as_bytes(),
        );
    }

    fn withdraw(&mut self, account_id: &AccountId, amount: Balance) -> bool{
        let mut account = self.internal_get_account(&account_id);
        assert!(
            account.unstaked >= amount,
            "Not enough unstaked balance to withdraw"
        );
        assert!(
            account.unstaked_available_epoch_height <= env::epoch_height(),
            "The unstaked balance is not yet available due to unstaking delay"
        );
        account.unstaked -= amount;
        let account_has_been_removed = self.internal_save_account(&account_id, &account);

        env::log(
            format!(
                "@{} withdrawing {}. New unstaked balance is {}",
                account_id, amount, account.unstaked
            )
            .as_bytes(),
        );

        return account_has_been_removed;
    }

    fn unstake(&mut self, account_id: &AccountId, amount: Balance){
        let mut account = self.internal_get_account(&account_id);

        assert!(
            self.total_staked_balance > 0,
            "The contract doesn't have staked balance"
        );
        // Calculate the number of shares required to unstake the given amount.
        // NOTE: The number of shares the account will pay is rounded up.
        let num_shares = self.num_shares_from_staked_amount_rounded_up(amount);
        assert!(
            num_shares > 0,
            "Invariant violation. The calculated number of \"stake\" shares for unstaking should be positive"
        );
        assert!(
            account.stake_shares >= num_shares,
            "Not enough staked balance to unstake"
        );

        // Calculating the amount of tokens the account will receive by unstaking the corresponding
        // number of "stake" shares, rounding up.
        let receive_amount = self.staked_amount_from_num_shares_rounded_up(num_shares);
        assert!(
            receive_amount > 0,
            "Invariant violation. Calculated staked amount must be positive, because \"stake\" share price should be at least 1"
        );

        account.stake_shares -= num_shares;
        account.unstaked += receive_amount;
        account.unstaked_available_epoch_height = env::epoch_height() + NUM_EPOCHS_TO_UNLOCK;
        self.internal_save_account(&account_id, &account);

        // The amount tokens that will be unstaked from the total to guarantee the "stake" share
        // price never decreases. The difference between `receive_amount` and `unstake_amount` is
        // paid from the allocated STAKE_SHARE_PRICE_GUARANTEE_FUND.
        let unstake_amount = self.staked_amount_from_num_shares_rounded_down(num_shares);

        self.total_staked_balance -= unstake_amount;
        self.total_stake_shares -= num_shares;

        env::log(
            format!(
                "@{} unstaking {}. Spent {} staking shares. Total {} unstaked balance and {} staking shares",
                account_id, receive_amount, num_shares, account.unstaked, account.stake_shares
            )
                .as_bytes(),
        );
        env::log(
            format!(
                "Contract inner staking pool total staked balance is {}. Total number of shares {}",
                self.total_staked_balance, self.total_stake_shares
            )
            .as_bytes(),
        );
    }

    fn get_account_unstaked_balance(&self, account_id: &AccountId) -> Balance{
        return self.internal_get_account(&account_id).unstaked;
    }

    fn get_account_info(&self, account_id: &AccountId) -> HumanReadableAccount{
        let account = self.internal_get_account(&account_id);
        return HumanReadableAccount {
            account_id: account_id.to_string(),
            unstaked_balance: account.unstaked.into(),
            staked_balance: self
                .staked_amount_from_num_shares_rounded_down(account.stake_shares)
                .into(),
            can_withdraw: account.unstaked_available_epoch_height <= env::epoch_height(),
            rewards_for_withdraw: 0.into()
        }
    }

    fn withdraw_not_staked_rewards(&mut self, _account_id: &AccountId) -> (Balance, bool){
        // Empty body because this pool doesnt have non staked rewards
        return (0, false);
    }
}

impl InnerStakingPoolWithoutRewardsRestaked{
    // Constructor
    pub fn new() -> Self{
        return Self {
            reward_per_token: Fraction::new(0, 0),
            total_staked_balance: 0,
            accounts: UnorderedMap::new(b"d".to_vec()),
        };
    }

    /// Inner method to get the given account or a new default value account.
    pub(crate) fn internal_get_account(&self, account_id: &AccountId) -> AccountWithReward {
        self.accounts.get(account_id).unwrap_or_default()
    }

    /// Inner method to save the given account for a given account ID.
    /// If the account balances are 0, the account is deleted instead to release storage.
    /// Returns true or false wether an element has been removed
    pub(crate) fn internal_save_account(&mut self, account_id: &AccountId, account: &AccountWithReward) -> bool {
        if account.unstaked > 0 || account.stake > 0 || account.reward_tally > 0 {
            self.accounts.insert(account_id, &account);
            return false;
        } else {
            self.accounts.remove(account_id);
            return true;
        }
    }

    pub(crate) fn distribute_reward(&mut self, reward:Balance){
        if reward == 0{
            return;
        }
        assert!(self.total_staked_balance > 0, "Cannot distribute reward when staked balance is 0 or below");
        self.reward_per_token.add(Fraction::new(reward, self.total_staked_balance));
    }

    pub(crate) fn compute_reward(&self, account: &AccountWithReward) -> Balance{
        if account.tally_below_zero {
            return self.reward_per_token.multiply(account.stake) + account.reward_tally;
        }else{
            return self.reward_per_token.multiply(account.stake) - account.reward_tally;
        }
    }
}

impl StakingPool for InnerStakingPoolWithoutRewardsRestaked{
    fn get_total_staked_balance(&self) -> Balance{
        return self.total_staked_balance;
    }

    fn stake(&mut self, account_id: &AccountId, amount: Balance){
        assert!(amount > 0, "Staking amount should be positive");
        let mut account = self.internal_get_account(&account_id);

        account.unstaked -= amount;
        account.stake += amount;
        account.add_to_tally(self.reward_per_token.multiply(amount));
        self.total_staked_balance+=amount;

        self.internal_save_account(account_id, &account);

        env::log(
            format!(
                "@{} staking {}. Total {} unstaked balance and {} staked amount",
                account_id, amount, account.unstaked, account.stake
            )
                .as_bytes(),
        );
    }

    fn deposit(&mut self, account_id: &AccountId, amount: Balance){
        let mut account = self.internal_get_account(&account_id);
        
        account.unstaked += amount;
        self.internal_save_account(&account_id, &account);

        env::log(
            format!(
                "@{} deposited {}. New unstaked balance is {}",
                account_id, amount, account.unstaked
            )
            .as_bytes(),
        );
    }

    fn withdraw(&mut self, account_id: &AccountId, amount: Balance) -> bool{
        let mut account = self.internal_get_account(&account_id);
        assert!(
            account.unstaked >= amount,
            "Not enough unstaked balance to withdraw"
        );
        assert!(
            account.unstaked_available_epoch_height <= env::epoch_height(),
            "The unstaked balance is not yet available due to unstaking delay"
        );
        account.unstaked -= amount;
        let account_has_been_removed = self.internal_save_account(&account_id, &account);

        env::log(
            format!(
                "@{} withdrawing {}. New unstaked balance is {}",
                account_id, amount, account.unstaked
            )
            .as_bytes(),
        );

        return account_has_been_removed;
    }

    fn unstake(&mut self, account_id: &AccountId, amount: Balance){
        let mut account = self.internal_get_account(&account_id);

        assert!(
            self.total_staked_balance > 0,
            "The contract doesn't have staked balance"
        );
        assert!(
            amount > 0,
            "The unstaking amount should be positive"
        );
        assert!(
            account.stake >= amount,
            "Not enough staked balance to unstake"
        );

        account.stake -= amount;
        account.unstaked += amount;
        account.subtract_from_tally(self.reward_per_token.multiply(amount));
        account.unstaked_available_epoch_height = env::epoch_height() + NUM_EPOCHS_TO_UNLOCK;
        self.internal_save_account(&account_id, &account);

        self.total_staked_balance -= amount;

        env::log(
            format!(
                "@{} unstaking {}. Total {} unstaked balance and {} staking amount",
                account_id, amount, account.unstaked, account.stake
            )
                .as_bytes(),
        );
        env::log(
            format!(
                "Contract inner staking pool total staked balance is {}",
                self.total_staked_balance
            )
            .as_bytes(),
        );
    }

    fn get_account_unstaked_balance(&self, account_id: &AccountId) -> Balance{
        return self.internal_get_account(account_id).unstaked;
    }

    fn get_account_info(&self, account_id: &AccountId) -> HumanReadableAccount{
        let account = self.internal_get_account(&account_id);
        return HumanReadableAccount {
            account_id: account_id.to_string(),
            unstaked_balance: account.unstaked.into(),
            staked_balance: account.stake.into(),
            can_withdraw: account.unstaked_available_epoch_height <= env::epoch_height(),
            rewards_for_withdraw: self.compute_reward(&account).into(),
        };
    }

    fn withdraw_not_staked_rewards(&mut self, account_id: &AccountId) -> (Balance, bool){
        let mut account = self.internal_get_account(&account_id);
        let reward = self.compute_reward(&account);
        account.reward_tally = self.reward_per_token.multiply(account.stake);
        let account_was_removed = self.internal_save_account(&account_id, &account);

        return (reward, account_was_removed);
    }
}