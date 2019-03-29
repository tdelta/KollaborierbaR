package proofutil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Observer;
import java.util.Optional;
import java.util.stream.Collectors;
import org.key_project.util.collection.ImmutableSet;

/**
 * Creates a wrapper around KeY functionality and provides methods to prove obligations
 *
 * @author Martin Hentschel, Jonas Belouadi
 */
public class KeYWrapper {
  private KeYEnvironment<?> env;
  private ProofResult results;
  private ProofScriptExecutor proofScriptExecutor;
  private Observer console;
  private Observer errorObserver;

  public KeYWrapper(String path, Observer console, Observer errorObserver) {
    final File location =
        new File("projects/" + path); // Path to the source code folder/file or to a *.proof file
    results = new ProofResult();

    this.console = console;
    this.errorObserver = errorObserver;
    proofScriptExecutor = new ProofScriptExecutor(console);

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
      env =
          KeYEnvironment.load(
              location, classPaths, bootClassPath, includes); // env.getLoadedProof() returns
      // performed proof if a *.proof
      // file is loaded
    } catch (ProblemLoaderException e) {
      errorObserver.update(
          null, "Couldn't process all relevant information for verification with KeY.");

      console.update(null, "Exception at '" + location + "':\n" + stackToString(e));

      System.out.println("Exception at '" + location + "':");
      e.printStackTrace();
    }
  }

  /**
   * Proves a single contract and adds the results to results class field
   *
   * @param obligationIdx the index of the contract in its source file
   * @param contract the contract that should be proven
   */
  private void proveContract(
      final int obligationIdx, final Contract contract, final Optional<String> macro) {
    // Perform proof
    Proof proof = null;

    if (env != null) {
      try {
        // Create proof
        proof = env.createProof(contract.createProofObl(env.getInitConfig(), contract));

        // Set proof strategy options
        StrategyProperties sp =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
        sp.setProperty(
            StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
            StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
        sp.setProperty(
            StrategyProperties.INF_FLOW_CHECK_PROPERTY, StrategyProperties.INF_FLOW_CHECK_FALSE);
        sp.setProperty(
            StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(
            StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(
            StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
        sp.setProperty(
            StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_DELAYED);
        sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY, StrategyProperties.MPS_MERGE);
        sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_EXPAND);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        sp.setProperty(
            StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
        sp.setProperty(StrategyProperties.VBT_PHASE, StrategyProperties.VBT_SYM_EX);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);

        // Make sure that the new options are used
        int maxSteps = 10000;
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
        proof.setActiveStrategy(
            proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));

        if (macro.isPresent()) {
          // Use macro for proof
          proofScriptExecutor.executeWithScript(macro.get(), proof);
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
              "Contract '"
                  + contract.getDisplayName()
                  + "' of "
                  + contract.getTarget()
                  + " is verified.",
              proofTree);
        } else {
          results.addFail(
              obligationIdx,
              contract.getTarget().toString(),
              "Contract '"
                  + contract.getDisplayName()
                  + "' of "
                  + contract.getTarget()
                  + " is still open.",
              proofTree,
              proof.openGoals().stream()
                  .map(
                      (Goal goal) -> {
                        final String sequent =
                            LogicPrinter.quickPrintSequent(goal.sequent(), env.getServices());

                        return new OpenGoalInfo(goal.getTime(), goal.toString(), sequent);
                      })
                  .collect(Collectors.toList()));
        }
      } catch (Exception e) {
        errorObserver.update(
            null,
            "Something went wrong at '"
                + contract.getDisplayName()
                + "' of "
                + contract.getTarget()
                + ".");

        console.update(
            null,
            "Exception at '"
                + contract.getDisplayName()
                + "' of "
                + contract.getTarget()
                + ":\n"
                + stackToString(e));

        System.out.println(
            "Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
        e.printStackTrace();
      } finally {
        if (proof != null) {
          proof.dispose(); // Ensure always that all instances of Proof are disposed
        }
      }
    }
  }

  /**
   * Converts a stacktrace to a string
   *
   * @param e the throwable whose stacktrace should be extracted as a string
   * @return th stacktrace as string
   */
  private String stackToString(final Throwable e) {
    // https://stackoverflow.com/questions/1149703/how-can-i-convert-a-stack-trace-to-a-string
    final StringWriter sw = new StringWriter();
    final PrintWriter pw = new PrintWriter(sw);
    e.printStackTrace(pw);

    return sw.toString();
  }

  /**
   * Proves all contracts that appear in a file
   *
   * @param className the path to the file relative to the projects folder
   * @return the results of the tried proofs
   */
  public ProofResult proveAllContracts(final String className, final Optional<String> macro) {
    if (env != null) {
      final KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(className);
      final ImmutableSet<IObserverFunction> targets =
          env.getSpecificationRepository().getContractTargets(keyType);

      // KeY lists obligations from bottom to top of the file.
      // We need to take this into account, when counting the
      // obligations from top to bottom, as the client does.

      // Therefore, we start with the maximum index.
      int currentObligationIdx =
          targets.stream()
                  .mapToInt(
                      target ->
                          env.getSpecificationRepository().getContracts(keyType, target).size())
                  .sum()
              - 1; // -1, since we start counting at 0

      for (final IObserverFunction target : targets) {
        final ImmutableSet<Contract> contracts =
            env.getSpecificationRepository().getContracts(keyType, target);

        int localObligationIdx = contracts.size() - 1;

        for (Contract contract : contracts) {
          proveContract(currentObligationIdx - localObligationIdx, contract, macro);

          localObligationIdx--;
        }

        currentObligationIdx -= contracts.size();
      }
    }

    return results;
  }

  public ProofResult proveContractByIdxs(final String className, final List<Integer> indices) {
    return proveContractByIdxs(className, indices, Optional.empty());
  }

  /**
   * Prove contracts by indices
   *
   * @param className the path to the file relative to the projects folder
   * @param indices the indices of the obligations to prove
   * @return the results of the tried proofs
   */
  public ProofResult proveContractByIdxs(
      final String className, final List<Integer> indices, Optional<String> macro) {
    if (env != null) {
      for (int index : indices) {
        final KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(className);
        final ImmutableSet<IObserverFunction> targets =
            env.getSpecificationRepository().getContractTargets(keyType);

        // KeY lists obligations from bottom to top of the file.
        // We need to take this into account, when counting the
        // obligations from top to bottom, as the client does.

        // Therefore, we start with the maximum index.
        int currentObligationIdx =
            targets.stream()
                    .mapToInt(
                        target ->
                            env.getSpecificationRepository().getContracts(keyType, target).size())
                    .sum()
                - 1; // -1, since we start counting at 0

        for (final IObserverFunction target : targets) {
          final ImmutableSet<Contract> contracts =
              env.getSpecificationRepository().getContracts(keyType, target);

          if (contracts.size() > 0 && currentObligationIdx + 1 - contracts.size() <= index) {
            proveContract(
                index,
                contracts
                    .toArray(new Contract[0])[contracts.size() - (currentObligationIdx - index) - 1
                    // obligations inside contract sets are sorted top to bottom
                    ],
                macro);

            break;
          } else {
            currentObligationIdx -= contracts.size();
          }
        }
      }
    }

    return results;
  }

  /** Indicates that the KeYEnvironment is disposed. */
  public void dispose() {
    if (env != null) {
      env.dispose();
    }
  }
}
