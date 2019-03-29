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
  private List<ObligationResult> stackTraces = new ArrayList<>();

  /**
   * Add a succeeded proof to the list
   *
   * @param msg the result message to be displayed
   */
  public void addSuccess(
      final int obligationIdx,
      final String methodName,
      final String msg,
      final ProofNode proofTree) {
    succeeded.add(
        new ObligationResult(
            obligationIdx,
            methodName,
            msg,
            proofTree,
            new ArrayList<>(0),
            ObligationResult.Kind.success));
  }

  /**
   * Add a failed proof to the list, used for proofs that couldn't be closed
   *
   * @param msg the result message to be displayed
   */
  public void addFail(
      final int obligationIdx,
      final String methodName,
      final String msg,
      final ProofNode proofTree,
      List<OpenGoalInfo> openGoals) {
    failed.add(
        new ObligationResult(
            obligationIdx, methodName, msg, proofTree, openGoals, ObligationResult.Kind.failure));
  }


  /**
   * Basic getter for contents
   *
   * @return succeeded proofs
   */
  public List<ObligationResult> getSucceeded() {
    return succeeded;
  }

  /**
   * Basic getter for contents
   *
   * @return failed proofs
   */
  public List<ObligationResult> getFailed() {
    return failed;
  }
}
