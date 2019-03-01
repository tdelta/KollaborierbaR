package proofutil;

import java.util.ArrayList;
import java.util.List;

/**
 * This class is used as a container for results of proofs carried out by KeY
 *
 * @author Jonas Belouadi
 */
public class ProofResult {
    private List<ObligationResult> succeeded = new ArrayList<>();
    private List<ObligationResult> failed = new ArrayList<>();
    private List<ObligationResult> errors = new ArrayList<>();
    private List<Obligation> openGoals = new ArrayList<>();
    private List<ObligationResult> stackTraces = new ArrayList<>();
    
    public List<ObligationResult> getStackTraces() {
		return stackTraces;
	}

	public void addStackTrace(final int obligationIdx, final String msg) {
		stackTraces.add(new ObligationResult(obligationIdx, msg));
	}

	/**
     * Add a succeded proof to the list
     * @param msg the result message to be displayed
     */
    public void addSuccess(final int obligationIdx, final String msg) {
        succeeded.add(new ObligationResult(obligationIdx, msg));
    }

    /**
     * Add a failed proof to the list, used for proofs that couldn't be closed
     * @param msg the result message to be displayed
     */
    public void addFail(final int obligationIdx, final String msg) {
        failed.add(new ObligationResult(obligationIdx, msg));
    }

    /**
     * Add an error message to the list, used whenever an exception occures
     * @param msg the result message to be displayed
     */
    public void addError(final int obligationIdx, final String msg) {
        errors.add(new ObligationResult(obligationIdx, msg));
    }

    /**
     * Add an open Goal to the list of open goals
     * (why am i even commenting on this?)
     * @param msg the goal to be added
     */
    public void addOpenGoal(final Obligation goal) {
        openGoals.add(goal);
    }

    /**
     * Basic getter for contents
     * @return succeded proofs
     */
    public List<ObligationResult> getSucceeded() {
        return succeeded;
    }

    /**
     * Basic getter for contents
     * @return failed proofs
     */
    public List<ObligationResult> getFailed() {
        return failed;
    }

    /**
     * Basic getter for contents
     * @return exception messages
     */
    public List<ObligationResult> getErrors() {
        return errors;
    }

    /**
     * Basic getter for open goals
     * @return open goals
     */
    public List<Obligation> getOpenGoals() {
        return openGoals;
    }
}
