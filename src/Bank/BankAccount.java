package Bank;
import java.io.Serializable;
import Exceptions.MaxBalance;
import Exceptions.MaxWithdraw;

public class BankAccount implements Serializable {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;
	//@ spec_public
	String name;
	//@ spec_public
	private double balance;
	//@ spec_public
	double min_balance;
	//@ spec_public
	String acc_num;

	//@ requires name != null && balance >= 0 && min_balance >= 0;
	//@ ensures this.name == name && this.balance == balance && this.min_balance == min_balance;
	//@ ensures acc_num != null;
	public BankAccount(String name, double balance, double min_balance) {
		this.name = name;
		this.balance = balance;
		this.min_balance = min_balance;
		acc_num = 10000 + (int)(Math.random()*89999) + "";
	}

	//@ requires amount >= 0;
	//@ ensures balance == \old(balance) + amount;
	public void deposit(double amount) {
		balance += amount;
	}

	//@ requires amount > 0;
	//@ requires (balance - amount) >= min_balance;
	//@ ensures balance == \old(balance) - amount;
	//@ signals (MaxBalance e) (balance - amount < min_balance);
	public void withdraw(double amount) throws MaxWithdraw, MaxBalance {
		if ((balance - amount) >= min_balance && amount < balance) {
			balance -= amount;
		} else {
			throw new MaxBalance("Insufficient Balance");
		}
	}

	//@ ensures \result == balance;
	public double getbalance() {
		return balance;
	}

	//@ ensures \result != null;
	@Override
	public String toString() {
		return "Name: " + name + ", Id: " + acc_num + ", Balance: " + balance +"Type:"+this.getClass();
	}
}