package Bank;

public class CurrentAccount extends BankAccount {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	//@ spec_public
	String tradeLicenseNumber;

	//@ requires name != null && balance >= 5000 && tradeLicenseNumber != null;
	//@ ensures this.tradeLicenseNumber == tradeLicenseNumber;
	//@ ensures super.getBalance() == balance;
	//@ signals (Exception e) balance < 5000;
	public CurrentAccount(String name, double balance, String tradeLicenseNumber) throws Exception {
		super(name, balance, 5000);
		this.tradeLicenseNumber = tradeLicenseNumber;
		if (balance < 5000) throw new Exception("Insufficient Balance");
	}
}
