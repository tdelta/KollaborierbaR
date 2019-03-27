package proofutil;

import java.util.List;

/**
 * Contains data describing the result of a KeY proof.
 *
 * <p>It is used for communicating proof results to clients and also storing them on the server, see
 * {@link server.ProofController}.
 *
 * <p>Eventually, most of this data will be displayed within UI elements of the client application.
 *
 * <p>Instances of this class are usually generated as part of {@link proofutil.ProofResult}.
 */
public class ObligationResult {
  /**
   * Encodes, whether the proof was successful, could not be closed (failure) or could not be run at
   * all (error).
   *
   * <p>The enum uses string data, since a verbose encoding is more useful considering this class is
   * used for network communication with clients.
   */
  public enum Kind {
    success("success"),
    failure("failure"),
    error("error");

    private final String value;

    Kind(final String value) {
      this.value = value;
    }

    public String getValue() {
      return value;
    }
  }

  private final int obligationIdx;
  private final String targetName;

  private final String resultMsg;
  private final ProofNode proofTree;
  private final List<OpenGoalInfo> openGoals;
  private final Kind kind;

  public ObligationResult(
      final int obligationIdx,
      final String targetName,
      final String resultMsg,
      final ProofNode proofTree,
      final List<OpenGoalInfo> openGoals,
      final Kind kind) {
    this.obligationIdx = obligationIdx;
    this.targetName = targetName;
    this.resultMsg = resultMsg;
    this.proofTree = proofTree;
    this.openGoals = openGoals;
    this.kind = kind;
  }

  /**
   * Returns the index of the proof obligation this proof result addresses.
   *
   * <p>When counting proof obligations within a Java source file from top to bottom, this is index
   * equals the count of the obligation described by this result.
   */
  public int getObligationIdx() {
    return obligationIdx;
  }

  /**
   * Returns the name of the target of this proof. Usually it is the name of the method, of which a
   * specification should be proven, resulting in this proof.
   */
  public String getTargetName() {
    return targetName;
  }

  /**
   * A human readable description, whether this proof result was successful or not. It can also
   * contain a stack trace, if this instance describes an error during a proof.
   */
  public String getResultMsg() {
    return resultMsg;
  }

  /**
   * A tree structure describing the steps of the proof. See also {@link ProofNode}.
   *
   * <p>It can return {@code null}, if no proof could be run at all (error case).
   */
  public ProofNode getProofTree() {
    return proofTree;
  }

  /**
   * A list of still open proof goals, if the proof could not be closed (proof failure case)
   *
   * <p>If there are no goals still open (proof success case), or the proof could not be run at all
   * (error case), it simply returns an empty list.
   */
  public List<OpenGoalInfo> getOpenGoals() {
    return openGoals;
  }

  /**
   * Reports, whether the proof was successful, could not be closed, or failed to run. See {@link
   * Kind}.
   */
  public Kind getKind() {
    return kind;
  }
}
