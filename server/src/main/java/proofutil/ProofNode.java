package proofutil;

import java.util.List;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.OneToMany;
import javax.persistence.FetchType;
import javax.persistence.CascadeType;

@Entity
public class ProofNode {
  public enum Kind {
    OpenProofTree("OpenProofTree"),
    ClosedProofTree("ClosedProofTree"),
    BranchNode("BranchNode"),
    OneStepSimplification("OneStepSimplification"),
    OpenGoal("OpenGoal"),
    ClosedGoal("ClosedGoal"),
    InteractiveGoal("InteractiveGoal"),
    LinkedGoal("LinkedGoal"),
    DefaultNode("DefaultNode");

    private final String value;

    Kind(final String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }
  }

  @Id
  @GeneratedValue(strategy = GenerationType.AUTO)
  private Integer id;

  private final String text;

  @OneToMany(fetch = FetchType.EAGER, cascade = CascadeType.ALL)
  private final List<ProofNode> children;
  private final Kind kind;
  private final String sequent;
  private final int serialNr;
  private final int oneStepId;

  public ProofNode(final String text, final List<ProofNode> children, final Kind kind, final String sequent, final int serialNr, final int oneStepId) {
    this.text = text;
    this.children = children;
    this.kind = kind;
    this.sequent = sequent;
    this.serialNr = serialNr;
    this.oneStepId = oneStepId;
  }

  public String getText() {
    return this.text;
  }

  public List<ProofNode> getChildren() {
    return this.children;
  }

  public Kind getKind() {
    return this.kind;
  }

  public String getSequent() {
    return this.sequent;
  }

  public int getSerialNr() {
    return this.serialNr;
  }

  public int getOneStepId() {
    return this.oneStepId;
  }
}
