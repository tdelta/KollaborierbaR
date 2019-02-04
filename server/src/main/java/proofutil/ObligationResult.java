package proofutil;

public class ObligationResult {
  private final int obligationIdx;
  private final String resultMsg;

  public ObligationResult(final int obligationIdx, final String resultMsg) {
    this.obligationIdx = obligationIdx;
    this.resultMsg = resultMsg;
  }

  public int getObligationIdx() {
    return obligationIdx;
  }

  public String getResultMsg() {
    return resultMsg;
  }
}
