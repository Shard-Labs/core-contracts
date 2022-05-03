use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::{Balance};
use uint::construct_uint;
construct_uint! {
    /// 256-bit unsigned integer.
    pub struct U256(4);
}

    #[derive(BorshDeserialize, BorshSerialize, PartialEq, Eq, Debug)]
    pub struct Fraction{
        pub numerator: u128,
        pub denominator: u128,
    }

    impl Default for Fraction{
        fn default() -> Self {
            Self {
                numerator: 0,
                denominator: 0,
            }
        }
    }

    impl Fraction{
        pub fn new(
            numerator: u128, 
            denominator: u128
        )-> Self{
            assert!((denominator == 0 && numerator == 0) 
            || (denominator != 0 && numerator != 0), "Denominator can only be 0 if numerator is 0");

            return Self{
                numerator: numerator,
                denominator: denominator
            };
        }
        pub fn add(&mut self, value: Fraction)-> &mut Self{
            if value == Fraction::default(){
                //do nothing
            }else if *self == Fraction::default(){
                self.numerator = value.numerator;
                self.denominator = value.denominator;
            }else {   
                // Finding greatest common divisor of the two denominators
                let gcd = self.greatest_common_divisior(self.denominator,value.denominator);      
                let new_denominator = ((U256::from(self.denominator) * U256::from(value.denominator)) / U256::from(gcd)).as_u128();
            
                // Changing the fractions to have same denominator
                // Numerator of the final fraction obtained
                self.numerator = (self.numerator) * (new_denominator / self.denominator) 
                        + (value.numerator) * (new_denominator / value.denominator);
                self.denominator = new_denominator;
            }
            // Calling function to convert final fraction
            // into it's simplest form
            self.simple_form();

            return self;
        }

        pub fn multiply(&self, value: Balance) -> Balance {
            if self.numerator == 0 && self.denominator == 0 {
                return 0;
            }

            return (U256::from(self.numerator) * U256::from(value) / U256::from(self.denominator)).as_u128()
        }

        fn simple_form(&mut self) -> &Self{
            if *self == Fraction::default(){
                return self;
            }
            let common_factor = self.greatest_common_divisior(self.numerator, self.denominator);
            self.denominator = self.denominator/common_factor;
            self.numerator = self.numerator/common_factor;

            return self;
        }

        fn greatest_common_divisior(
            &self, 
            a: u128, 
            b: u128
        ) -> u128{
            if a == 0{
                return b;
            }
            return self.greatest_common_divisior(b%a, a);
        }
    }