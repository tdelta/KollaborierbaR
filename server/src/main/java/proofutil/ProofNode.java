package proofutil;

import java.util.List;

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

  private final String text;
  private final List<ProofNode> children;
  private final Kind kind;
  private final String sequent;

  public ProofNode(final String text, final List<ProofNode> children, final Kind kind, final String sequent) {
    this.text = text;
    this.children = children;
    this.kind = kind;
    this.sequent = sequent;
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
}
