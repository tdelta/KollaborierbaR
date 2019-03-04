package proofutil;

public class ObligationResult {
  private final int obligationIdx;
  private final String resultMsg;
  private final ProofNode proofTree;

  public ObligationResult(final int obligationIdx, final String resultMsg, final ProofNode proofTree) {
    this.obligationIdx = obligationIdx;
    this.resultMsg = resultMsg;
    this.proofTree = proofTree;
  }

  public int getObligationIdx() {
    return obligationIdx;
  }

  public String getResultMsg() {
    return resultMsg;
  }

  public ProofNode getProofTree() {
    return proofTree;
  }
}
