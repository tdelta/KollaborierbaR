package proofutil;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToOne;
import javax.persistence.ManyToOne;
import javax.persistence.CascadeType;

import repository.MethodContract;

@Entity
public class ObligationResult {

  @Id
  @GeneratedValue
  private Long id;

  private final int obligationIdx;
  private final String resultMsg;

  @ManyToOne(cascade = CascadeType.ALL)
  private MethodContract methodContract;

  @OneToOne(cascade = CascadeType.ALL)
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

  public void setMethodContract(MethodContract methodContract){
    this.methodContract = methodContract;
  }
}
