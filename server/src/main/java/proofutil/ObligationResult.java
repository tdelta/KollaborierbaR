package proofutil;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToOne;
import javax.persistence.ManyToOne;
import javax.persistence.CascadeType;

import repository.MethodContract;

@Entity(name = "ObligationResult")
public class ObligationResult {

  @Id
  @GeneratedValue
  private Long id;

  private int obligationIdx;
  private String resultMsg;

  @ManyToOne
  private MethodContract methodContract;

  @OneToOne(cascade = CascadeType.ALL)
  private ProofNode proofTree;

  public ObligationResult(){}

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
