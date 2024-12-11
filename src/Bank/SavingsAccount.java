package Bank;
import Exceptions.MaxBalance;
import Exceptions.MaxWithdraw;

public class SavingsAccount extends BankAccount {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;
	//@ spec_public
	float rate = .05f;
	//@ spec_public
	double maxWithLimit;

	//@ requires name != null && balance >= 2000 && maxWithLimit > 0;
	//@ ensures this.name == name && this.maxWithLimit == maxWithLimit;
	//@ ensures getbalance() == balance;
	public SavingsAccount(String name, double balance, double maxWithLimit) {
		super(name, balance, 2000);
		this.maxWithLimit = maxWithLimit;
	}

	//@ ensures \result == getbalance() + (getbalance() * rate);
	public double getNetBalance() {
		double NetBalance = getbalance() + (getbalance() * rate);
		return NetBalance;
	}

	//@ requires amount > 0 && amount <= maxWithLimit;
	//@ ensures \old(getbalance()) >= amount;
	//@ signals (MaxWithdraw e) amount > maxWithLimit;
	//@ signals (MaxBalance e) \old(getbalance()) - amount < min_balance;
	public void withdraw(double amount) throws MaxWithdraw, MaxBalance {
		if (amount < maxWithLimit) {
			super.withdraw(amount);
		} else {
			throw new MaxWithdraw("Maximum Withdraw Limit Exceed");
		}
	}
}
