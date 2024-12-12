package Bank;

import java.io.Serializable;
import javax.swing.DefaultListModel;

import Exceptions.AccNotFound;
import Exceptions.InvalidAmount;
import Exceptions.MaxBalance;
import Exceptions.MaxWithdraw;

public class Bank implements Serializable {
    private static final long serialVersionUID = 1L;
    //@ private invariant accounts != null && accounts.length == 100;
    //@ spec_public
    private BankAccount[] accounts = new BankAccount[100];

    //@ requires acc != null;
    //@ ensures \result >= 0 && \result < 100;
    //@ ensures \result == (\exists int i; 0 <= i && i < 100; accounts[i] == acc ? i : -1);
    //@ pure
    public int addAccount(BankAccount acc) {
        int i = 0;
        //@ maintaining i >= 0 && i <= 100;
        //@ maintaining (\forall int j; 0 <= j && j < i; accounts[j] != null);
        for (i = 0; i < 100; i++) {
            if (accounts[i] == null) {
                break;
            }
        }
        accounts[i] = acc;
        return i;
    }

    //@ requires name != null && balance >= 0 && maxWithLimit >= 0;
    //@ ensures \result >= 0 && \result < 100;
    public int addAccount(String name, double balance, double maxWithLimit) {
        SavingsAccount acc = new SavingsAccount(name, balance, maxWithLimit);
        return this.addAccount(acc);
    }

    //@ requires name != null && balance >= 0 && tradeLicense != null;
    //@ ensures \result >= 0 && \result < 100;
    public int addAccount(String name, double balance, String tradeLicense) throws Exception {
        CurrentAccount acc = new CurrentAccount(name, balance, tradeLicense);
        return this.addAccount(acc);
    }

    //@ requires name != null && institutionName != null && balance >= 0 && min_balance >= 0;
    //@ ensures \result >= 0 && \result < 100;
    public int addAccount(String name, String institutionName, double balance, double min_balance) {
        StudentAccount acc = new StudentAccount(name, balance, institutionName);
        return this.addAccount(acc);
    }

    //@ requires aacountNum != null;
    //@ ensures \result == null || \result.acc_num.equals(aacountNum);
    //@ pure
    public BankAccount findAccount(String aacountNum) {
        int i;
        //@ maintaining i >= 0 && i <= 100;
        //@ maintaining (\forall int j; 0 <= j && j < i; getAccounts()[j] != null);
        for (i = 0; i < 100; i++) {
            if (getAccounts()[i] == null) {
                break;
            }
            if (getAccounts()[i].acc_num.equals(aacountNum)) {
                return getAccounts()[i];
            }
        }
        return null;
    }

    //@ requires amt >= 0 && aacountNum != null;
    //@ ensures findAccount(aacountNum) != null;
    //@ pure
    public void deposit(String aacountNum, double amt) throws InvalidAmount, AccNotFound {
        if (amt < 0) {
            throw new InvalidAmount("Invalid Deposit amount");
        }
        BankAccount temp = findAccount(aacountNum);
        if (temp == null) {
            throw new AccNotFound("Account Not Found");
        }
        if (temp != null) {
            temp.deposit(amt);
        }
    }

    //@ requires amt > 0 && aacountNum != null;
    //@ ensures findAccount(aacountNum) != null;
    //@ ensures (\forall BankAccount b; b.acc_num.equals(aacountNum); b.getbalance() >= amt);
    public void withdraw(String aacountNum, double amt) throws MaxBalance, AccNotFound, MaxWithdraw, InvalidAmount {
        BankAccount temp = findAccount(aacountNum);

        if (temp == null) {
            throw new AccNotFound("Account Not Found");
        }

        if (amt <= 0) {
            throw new InvalidAmount("Invalid Amount");
        }

        if (amt > temp.getbalance()) {
            throw new MaxBalance("Insufficient Balance");
        }
        if (temp != null) {
            temp.withdraw(amt);
        }
    }

    //@ ensures \result != null;
    public DefaultListModel<String> display() {
        DefaultListModel<String> list = new DefaultListModel<String>();
        int i;

        //@ maintaining i >= 0 && i <= 100;

