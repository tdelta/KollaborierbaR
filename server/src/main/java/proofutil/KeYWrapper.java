package proofutil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;

import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;

/**
 * Basic KeY stub, that tries to prove all contracts in a file
 *
 * @author Martin Hentschel, Jonas Belouadi
 */
public class KeYWrapper {
	KeYEnvironment<?> env;
	ProofResult results;

	public KeYWrapper(String path) {
		final File location = new File("projects/" + path); // Path to the source code folder/file or to a *.proof file
		results = new ProofResult();

		try {
			List<File> classPaths = null; // Optionally: Additional specifications for API classes
			File bootClassPath = null; // Optionally: Different default specifications for Java API
			List<File> includes = null; // Optionally: Additional includes to consider

			// Ensure that Taclets are parsed
			if (!ProofSettings.isChoiceSettingInitialised()) {
				KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
				env.dispose();
			}

			// Set Taclet options
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
			HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
			newSettings.putAll(MiscTools.getDefaultTacletOptions());
			choiceSettings.setDefaultChoices(newSettings);

			// Load source code
			env = KeYEnvironment.load(location, classPaths, bootClassPath, includes); // env.getLoadedProof() returns
																						// performed proof if a *.proof
																						// file is loaded
		} catch (ProblemLoaderException e) {
			results.addError(-1, "Couldn't process all relevant information for verification with KeY.", null);
			System.out.println("Exception at '" + location + "':");
			e.printStackTrace();
		}
	}

	public void proveContract(final int obligationIdx, final Contract contract) {
		// Perform proof
		Proof proof = null;

		if (env != null) {
			try {
				// Create proof
				proof = env.createProof(contract.createProofObl(env.getInitConfig(), contract));

				// Set proof strategy options
				StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
				sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
				sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
				sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
				sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
				sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
				proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);

				// Make sure that the new options are used
				int maxSteps = 10000;
				ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
				ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
				proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
				proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));

				// Start auto mode
				env.getUi().getProofControl().startAndWaitForAutoMode(proof);

				// Show proof result
				final boolean closed = proof.openGoals().isEmpty();

        final ProofNode proofTree = generateProofTree(proof);

				if (closed) {
					results.addSuccess(
              obligationIdx,
              "Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is verified.",
              proofTree
          );
        }

				else {
					results.addFail(
              obligationIdx,
              "Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is still open.",
              proofTree
          );
				
          for (Goal goal: proof.openGoals()) {
            results.addOpenGoal(new Obligation(goal.getTime(), goal.toString()));
          }
				}
			} catch (ProofInputException e) {
				results.addError(
            obligationIdx,
						"Something went wrong at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ".",
            null
        );

				System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
				e.printStackTrace();
			} finally {
				if (proof != null) {
					proof.dispose(); // Ensure always that all instances of Proof are disposed
				}
			}
		}
	}

	public ProofResult proveAllContracts(String className) {
		if (env != null) {
			final KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(className);
			final ImmutableSet<IObserverFunction> targets =
        env.getSpecificationRepository().getContractTargets(keyType);

      // KeY lists obligations from bottom to top of the file.
      // We need to take this into account, when counting the
      // obligations from top to bottom, as the client does.

      // Therefore, we start with the maximum index.
      int currentObligationIdx = targets
        .stream()
        .mapToInt(target -> 
              env
                .getSpecificationRepository()
                .getContracts(keyType, target)
                .size()
            )
        .sum() - 1; // -1, since we start counting at 0

			for (final IObserverFunction target : targets) {
				final ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(keyType, target);

        int localObligationIdx = contracts.size() - 1;

				for (Contract contract : contracts) {
					proveContract(currentObligationIdx - localObligationIdx, contract);

          localObligationIdx--;
				}

        currentObligationIdx -= contracts.size();
			}
		}

		return results;
	}

  public ProofResult proveContractByIndex(final String className, final int index) {
    if (env != null) {
      final KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(className);
      final ImmutableSet<IObserverFunction> targets =
          env.getSpecificationRepository().getContractTargets(keyType);

      // KeY lists obligations from bottom to top of the file.
      // We need to take this into account, when counting the
      // obligations from top to bottom, as the client does.

      // Therefore, we start with the maximum index.
      int currentObligationIdx = targets
        .stream()
        .mapToInt(target -> 
              env
                .getSpecificationRepository()
                .getContracts(keyType, target)
                .size()
            )
        .sum() - 1; // -1, since we start counting at 0

      for (final IObserverFunction target : targets) {
        final ImmutableSet<Contract> contracts =
            env.getSpecificationRepository().getContracts(keyType, target);

        if (contracts.size() > 0 && currentObligationIdx + 1 - contracts.size() <= index) {
          proveContract(index, contracts.toArray(new Contract[0])[
              contracts.size() - (currentObligationIdx - index) - 1
              // obligations inside contract sets are sorted top to bottom
          ]);

          return results;
        }

        else {
          currentObligationIdx -= contracts.size();
        }
      }
    }

    return results;
  }

	public void dispose() {
		if (env != null)
			env.dispose();
	}

  private ProofNode generateProofTree(final Proof proof) {
    final ProofNode.Kind kind;

    if (proof.closed()) {
      kind = ProofNode.Kind.ClosedProofTree;
    }

    else {
      kind = ProofNode.Kind.OpenProofTree;
    }

    return generateBranchNode(proof.root(), "Proof Tree", kind);
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

    return new ProofNode(
        label,
        children,
        kind
    );
  }

  private ProofNode generateOneStepNode(final Services services, final RuleApp app) {
    final String prettySubTerm =
      LogicPrinter.quickPrintTerm(app.posInOccurrence().subTerm(), services);

    return new ProofNode(
        app.rule().name() + " ON " + prettySubTerm,
        new ArrayList<ProofNode>(0),
        ProofNode.Kind.OneStepSimplification
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
                generateOneStepNode(node.proof().getServices(), protocol.get(i))
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

    return new ProofNode(
        node.serialNr() + ":" + node.name(),
        children,
        kind
    );
  }
}
