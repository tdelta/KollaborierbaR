package proofutil;

import java.util.List;

public class ProofNode {
  private final String text;
  private final List<ProofNode> children;

  public ProofNode(final String text, final List<ProofNode> children) {
    this.text = text;
    this.children = children;
  }

  public String getText() {
    return this.text;
  }

  public List<ProofNode> getChildren() {
    return this.children;
  }
}
