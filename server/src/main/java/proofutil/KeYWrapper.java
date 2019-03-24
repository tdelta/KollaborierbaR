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
import de.uka.ilkd.key.macros.scripts.ScriptException;

import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.Optional;

/**
 * Basic KeY stub, that tries to prove all contracts in a file
 *
 * @author Martin Hentschel, Jonas Belouadi
 */
public class KeYWrapper {
	KeYEnvironment<?> env;
	ProofResult results;
  ProofScriptExecutor proofScriptExecutor = new ProofScriptExecutor();

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
			results.addError(
          -1, 
          "unknown",
          "Couldn't process all relevant information for verification with KeY.",
          null
      );

			results.addStackTrace(
          -1,
          "unknown",
          "Exception at '" + location + "':\n" + stackToString(e)
      );

			System.out.println("Exception at '" + location + "':");
			e.printStackTrace();
		}
	}

	public void proveContract(final int obligationIdx, final Contract contract, Optional<String> macro) {
		// Perform proof
		Proof proof = null;

		if (env != null) {
			try {
				// Create proof
				proof = env.createProof(contract.createProofObl(env.getInitConfig(), contract));

				// Set proof strategy options
				StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();

        sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY,StrategyProperties.QUERYAXIOM_ON);
        //sp.setProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY1,StrategyProperties.USER_TACLETS_OFF);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        //sp.setProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY2,StrategyProperties.USER_TACLETS_OFF);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,StrategyProperties.LOOP_NONE);
        sp.setProperty(StrategyProperties.INF_FLOW_CHECK_PROPERTY,StrategyProperties.INF_FLOW_CHECK_FALSE);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,StrategyProperties.STOPMODE_DEFAULT);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,StrategyProperties.CLASS_AXIOM_DELAYED);
        sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY,StrategyProperties.MPS_MERGE);
        //sp.setProperty(StrategyProperties.QUERY_NEW_OPTIONS_KEY,StrategyProperties.QUERY_RESTRICTED);
        sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY,StrategyProperties.BLOCK_EXPAND);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,StrategyProperties.METHOD_CONTRACT);
        //sp.setProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY3,StrategyProperties.USER_TACLETS_OFF);
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,StrategyProperties.OSS_OFF);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,StrategyProperties.SPLITTING_DELAYED);
        sp.setProperty(StrategyProperties.VBT_PHASE,StrategyProperties.VBT_SYM_EX);

				proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);

				// Make sure that the new options are used
				int maxSteps = 10000;
				ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
				ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
				proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
				proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));

        if(macro.isPresent()){
            proof = proofScriptExecutor.executeWithScript(macro.get(),proof);
        } else {
				    // Start auto mode
				    env.getUi().getProofControl().startAndWaitForAutoMode(proof);
        }

				// Show proof result
				final boolean closed = proof.openGoals().isEmpty();

        final ProofNode proofTree;
        {
          final ProofTreeBuilder proofTreeBuilder = new ProofTreeBuilder();
          proofTree = proofTreeBuilder.generateProofTree(proof);
        }

				if (closed) {
					results.addSuccess(
              obligationIdx,
              contract.getTarget().toString(),
              "Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is verified.",
              proofTree
          );
        }

				else {
					results.addFail(
              obligationIdx,
              contract.getTarget().toString(),
              "Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is still open.",
              proofTree,
              proof
                .openGoals()
                .stream()
                .map((Goal goal) -> {
                  final String sequent = LogicPrinter.quickPrintSequent(goal.sequent(),env.getServices());

                  return new OpenGoalInfo(goal.getTime(), goal.toString(),sequent);
                })
                .collect(Collectors.toList())
          );
				}
			} catch (Exception e) {
				results.addError(
			             obligationIdx,
                   "unknown",
                   "Something went wrong at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ".",
                   null
        );

				results.addStackTrace(
            obligationIdx,
            contract.getTarget().toString(),
            "Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":\n" + KeYWrapper.stackToString(e)
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
	
	public static String stackToString(final Throwable e) {
		//https://stackoverflow.com/questions/1149703/how-can-i-convert-a-stack-trace-to-a-string
		final StringWriter sw = new StringWriter();
		final PrintWriter pw = new PrintWriter(sw);
		e.printStackTrace(pw);

		return sw.toString();
	}

  public ProofResult proveAllContracts(String className){
    return proveAllContracts(className, Optional.empty());
  }  

	public ProofResult proveAllContracts(String className, Optional<String> macro) {
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
					proveContract(currentObligationIdx - localObligationIdx, contract,macro);

          localObligationIdx--;
				}

        currentObligationIdx -= contracts.size();
			}
		}

		return results;
	}

  public ProofResult proveContractByIdxs(final String className, final List<Integer> indices){
    return proveContractByIdxs(className, indices, Optional.empty());
  }

  public ProofResult proveContractByIdxs(final String className, final List<Integer> indices, Optional<String> macro) {
    if (env != null) {
      for (int index: indices) {
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
	        ],macro);
	
	        break;
	      }
	
	      else {
	        currentObligationIdx -= contracts.size();
	      }
	    }
	    }
    }

    return results;
  }

	public void dispose() {
		if (env != null)
			env.dispose();
	}
}
