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

  public ProofNode(final String text, final List<ProofNode> children, final Kind kind) {
    this.text = text;
    this.children = children;
    this.kind = kind;
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
}
