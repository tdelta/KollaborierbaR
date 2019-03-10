package proofutil;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.java.Services;

import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;

class ProofTreeBuilder {
  public ProofTreeBuilder() { }

  public ProofNode generateProofTree(final Proof proof) {
    final ProofNode.Kind kind;

    if (proof.closed()) {
      kind = ProofNode.Kind.ClosedProofTree;
    }

    else {
      kind = ProofNode.Kind.OpenProofTree;
    }

    return generateBranchNode(proof.root(), proof.name().toString(), kind);
  }

  private Node findChild (Node n) {
      if ( n.childrenCount () == 1 ) return n.child ( 0 );
      
      Node nextN = null;
      for ( int i = 0; i != n.childrenCount (); ++i ) {
          if ( ! n.child ( i ).isClosed() ) {
              if ( nextN != null ) return null;
              nextN = n.child ( i );
          }
      }
  
      return nextN;
  }

  private ProofNode generateBranchNode(final Node node, final String forcedLabel, final ProofNode.Kind forcedKind) {
    final String label;
    {
      if (forcedLabel != null) {
        label = forcedLabel;
      }

      else if(node.getNodeInfo().getBranchLabel() != null) {
        label = node.getNodeInfo().getBranchLabel();
      }

      else {
        label = "(Unlabelled node)";
      }
    }

    final ProofNode.Kind kind;
    if (forcedKind == null) {
      kind = ProofNode.Kind.BranchNode;
    }

    else {
      kind = forcedKind;
    }

    final List<ProofNode> children = new LinkedList<>();
    {
      Node currentNode = node;

      while (true) {
          children.add(generateDefaultNode(currentNode));

          final Node nextN = findChild(currentNode);
          if (nextN == null) {
            break;
          }

          currentNode = nextN;
      }

      for (int i = 0; i != currentNode.childrenCount(); ++i) {
          if (!currentNode.child(i).isClosed()) {
              children.add(generateBranchNode(currentNode.child(i), null, null));
          }
      }
    }

    String sequent = LogicPrinter.quickPrintSequent(node.sequent(),node.proof().getServices());

    return new ProofNode(
        label,
        children,
        kind,
        sequent,
        node.serialNr(),
        0
    );
  }

  private ProofNode generateOneStepNode(final Services services, final RuleApp app, final int parentSerialNr, final int oneStepId) {
    final String prettySubTerm =
      LogicPrinter.quickPrintTerm(app.posInOccurrence().subTerm(), services);

    return new ProofNode(
        app.rule().name() + " ON " + prettySubTerm,
        new ArrayList<ProofNode>(0),
        ProofNode.Kind.OneStepSimplification,
        "",
        parentSerialNr,
        oneStepId
    );
  }

  private ProofNode generateDefaultNode(final Node node) {
    final List<ProofNode> children;

    if (node == null || !(node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp)) {
      children = new ArrayList<>(0);
    }

    else {
      final Protocol protocol =
        ((OneStepSimplifierRuleApp)node.getAppliedRuleApp()).getProtocol();

      if(protocol != null) {
          final int numChildren = protocol.size();
          children = new ArrayList<>(numChildren);

          for (int i = 0; i < numChildren; ++i) {
            children.add(
                generateOneStepNode(node.proof().getServices(), protocol.get(i), node.serialNr(), i)
            );
          }
      }

      else {
        children = new ArrayList<>(0);
      }
    }

    final ProofNode.Kind kind;
    if (node.leaf()) {
      final Goal goal = node.proof().getGoal(node);

      if ( goal == null || node.isClosed() ) {
        kind = ProofNode.Kind.ClosedGoal;
      } else {
        if ( goal.isLinked() ) {
          kind = ProofNode.Kind.LinkedGoal;
        } else if ( !goal.isAutomatic() ) {
          kind = ProofNode.Kind.InteractiveGoal;
        } else {
          kind = ProofNode.Kind.OpenGoal;
        }
      }
    }

    else {
      kind = ProofNode.Kind.DefaultNode;
    }

    String sequent = LogicPrinter.quickPrintSequent(node.sequent(),node.proof().getServices());

    return new ProofNode(
        node.serialNr() + ":" + node.name(),
        children,
        kind,
        sequent,
        node.serialNr(),
        0
    );
  }
}
