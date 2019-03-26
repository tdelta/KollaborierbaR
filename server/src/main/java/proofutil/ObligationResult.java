package proofutil;

import com.fasterxml.jackson.annotation.JsonIgnore;
import java.util.List;
import javax.persistence.CascadeType;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.OneToMany;
import javax.persistence.OneToOne;
import repository.MethodContract;

/**
 * Definition for a table in the database and the format of the response for api routes. Fields
 * annotated with JsonIgnore will not be included in network responses.
 */
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

  @JsonIgnore @Id @GeneratedValue private Long id;

  @JsonIgnore @ManyToOne private MethodContract methodContract;

  private String resultMsg;

  @OneToOne(cascade = CascadeType.ALL)
  private ProofNode proofTree;

  @OneToMany(cascade = CascadeType.ALL)
  private List<OpenGoalInfo> openGoals;

  private Kind kind;
  private String targetName;
  private int obligationIdx;

  /** Default constructor needed for hibernate */
  public ObligationResult() {}

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
   * Sets the method contract (foreign key in the database) that this obligation result belongs to
   */
  public void setMethodContract(MethodContract methodContract) {
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

  public String getTargetName() {
    return targetName;
  }

  public Kind getKind() {
    return kind;
  }

  /** @return primary key in the database */
  public Long getId() {
    return id;
  }

  public int getObligationIdx() {
    return obligationIdx;
  }
}
