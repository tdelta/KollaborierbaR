package proofutil;

import java.util.List;

public class ObligationResult {
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

  public int getObligationIdx() {
    return obligationIdx;
  }

  public String getTargetName() {
    return targetName;
  }

  public String getResultMsg() {
    return resultMsg;
  }

  public ProofNode getProofTree() {
    return proofTree;
  }

  public List<OpenGoalInfo> getOpenGoals() {
    return openGoals;
  }

  public Kind getKind() {
    return kind;
  }
}
