package proofutil;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToOne;
import javax.persistence.ManyToOne;
import javax.persistence.OneToMany;
import javax.persistence.CascadeType;

import com.fasterxml.jackson.annotation.JsonIgnore;

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

  @JsonIgnore
  @Id
  @GeneratedValue
  private Long id;

  @JsonIgnore
  @ManyToOne
  private MethodContract methodContract;

  private String resultMsg;

  @OneToOne(cascade = CascadeType.ALL)
  private ProofNode proofTree;

  @OneToMany(cascade = CascadeType.ALL)
  private List<OpenGoalInfo> openGoals;
  private Kind kind;
  private String targetName;
  private int obligationIdx;

  public ObligationResult() {}

  public ObligationResult(final int obligationIdx, final String targetName, final String resultMsg, final ProofNode proofTree, final List<OpenGoalInfo> openGoals, final Kind kind) {
    this.obligationIdx = obligationIdx;
    this.targetName = targetName;
    this.resultMsg = resultMsg;
    this.proofTree = proofTree;
    this.openGoals = openGoals;
    this.kind = kind;
  }

  public void setMethodContract(MethodContract methodContract){
    this.methodContract = methodContract;
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

  public String getTargetName(){
    return targetName;
  }

  public Kind getKind() {
    return kind;
  }

  public Long getId(){
    return id;
  }

  public int getObligationIdx(){
    return obligationIdx;
  }
}
