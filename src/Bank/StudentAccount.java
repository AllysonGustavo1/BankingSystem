package Bank;

public class StudentAccount extends SavingsAccount {
	/**
	 *
	 */
	private static final long serialVersionUID = 1L;
	//@ spec_public
	String institutionName;

	//@ requires name != null && balance >= 100 && institutionName != null;
	//@ ensures this.name == name && this.institutionName == institutionName;
	//@ ensures this.min_balance == 100;
	public StudentAccount(String name, double balance, String institutionName) {
		super(name, balance, 20000);
		min_balance = 100;
		this.institutionName = institutionName;
	}
}
