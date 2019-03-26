package proofutil;

import java.util.List;

/**
 * Representation of one step or branch in a KeY proof. Since it also contains it children, it can
 * be used to represent an entire proof tree.
 *
 * <p>Its primary purpose is to conveniently provide all data to the client, the client needs for
 * its KeY features, without replicating many of KeYs data structures on the client side.
 *
 * <p>Usually, ProofNodes are constructed by {@link proofutil.ProofTreeBuilder}.
 */
public class ProofNode {
  /**
   * Encodes different types of nodes.
   *
   * <p>The enum uses string data, since a verbose encoding is more useful considering this class is
   * used for network communication with clients.
   */
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
  private final int serialNr;
  private final int oneStepId;

  public ProofNode(
      final String text,
      final List<ProofNode> children,
      final Kind kind,
      final String sequent,
      final int serialNr,
      final int oneStepId) {
    this.text = text;
    this.children = children;
    this.kind = kind;
    this.sequent = sequent;
    this.serialNr = serialNr;
    this.oneStepId = oneStepId;
  }

  /**
   * Human readable text, intended to be shown as a short summary of the node when displayed in tree
   * views.
   */
  public String getText() {
    return this.text;
  }

  /** Returns a list of all children of this node. If there are none, returns an empty list. */
  public List<ProofNode> getChildren() {
    return this.children;
  }

  /** Type of node, see {@link Kind} */
  public Kind getKind() {
    return this.kind;
  }

  /**
   * {@link de.uka.ilkd.key.proof.Node#sequent} rendered using {@link
   * de.uka.ilkd.key.pp.LogicPrinter#quickPrintSequent}.
   */
  public String getSequent() {
    return this.sequent;
  }

  /**
   * Unique id of this node within the proof tree, if its parent is not a One Step Simplification.
   * If its parent is a One Step simplification, it forms a unique key together with {@link
   * #getOneStepId}.
   */
  public int getSerialNr() {
    return this.serialNr;
  }

  /**
   * Unique id of this node relative to all its siblings, if it is a child of a One Step
   * Simplification node. Otherwise, it always equals 0. Together with {@link #getSerialNr}, this
   * field forms a unique id within the whole proof tree.
   */
  public int getOneStepId() {
    return this.oneStepId;
  }
}
