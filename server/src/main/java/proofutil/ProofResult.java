package proofutil;

import java.util.ArrayList;
import java.util.List;

/**
 * This class is used as a container for results of proofs carried out by KeY
 *
 * @author Jonas Belouadi
 */
public class ProofResult {
  private List<String> succeeded = new ArrayList<String>();
  private List<String> failed = new ArrayList<String>();
  private List<String> errors = new ArrayList<String>();

  /**
   * Add a succeded proof to the list
   *
   * @param msg the result message to be displayed
   */
  public void addSuccess(String msg) {
    succeeded.add(msg);
  }

  /**
   * Add a failed proof to the list, used for proofs that couldn't be closed
   *
   * @param msg the result message to be displayed
   */
  public void addFail(String msg) {
    failed.add(msg);
  }

  /**
   * Add an error message to the list, used whenever an exception occures
   *
   * @param msg the result message to be displayed
   */
  public void addError(String msg) {
    errors.add(msg);
  }

  /**
   * Basic getter for contents
   *
   * @return succeded proofs
   */
  public List<String> getSucceeded() {
    return succeeded;
  }

  /**
   * Basic getter for contents
   *
   * @return failed proofs
   */
  public List<String> getFailed() {
    return failed;
  }

  /**
   * Basic getter for contents
   *
   * @return exception messages
   */
  public List<String> getErrors() {
    return errors;
  }
}
