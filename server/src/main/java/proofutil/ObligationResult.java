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
 *
 * <p>Contains data describing the result of a KeY proof.
 *
 * <p>Eventually, most of this data will be displayed within UI elements of the client application.
 *
 * <p>Instances of this class are usually generated as part of {@link proofutil.ProofResult}.
 */
@Entity(name = "ObligationResult")
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

  /** @return primary key in the database */
  public Long getId() {
    return id;
  }
}
