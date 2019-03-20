package proofutil;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToOne;
import javax.persistence.ManyToOne;
import javax.persistence.CascadeType;

import repository.MethodContract;

import java.util.List;

@Entity(name = "ObligationResult")
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

  @Id
  @GeneratedValue
  private Long id;

  @ManyToOne
  private MethodContract methodContract;

  private String resultMsg;

  @OneToOne(cascade = CascadeType.ALL)
  private ProofNode proofTree;

  private List<OpenGoalInfo> openGoals;
  private Kind kind;

  public ObligationResult() {}

  public ObligationResult(final int obligationIdx, final String targetName, final String resultMsg, final ProofNode proofTree, final List<OpenGoalInfo> openGoals, final Kind kind) {
    this.obligationIdx = obligationIdx;
    this.targetName = targetName;
    this.resultMsg = resultMsg;
    this.proofTree = proofTree;
    this.openGoals = openGoals;
    this.kind = kind;
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

  public List<OpenGoalInfo> getOpenGoals() {
    return openGoals;
  }

  public Kind getKind() {
    return kind;
  }
}
