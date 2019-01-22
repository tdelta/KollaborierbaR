package server;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.servlet.http.HttpServletRequest;

import org.key_project.util.collection.ImmutableSet;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.servlet.HandlerMapping;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

import proofutil.ProofResult;

/**
 * Basic KeY stub, that tries to prove all contracts in a file
 * @author Martin Hentschel, Jonas Belouadi
 */
@RestController
@CrossOrigin
@RequestMapping("/proof")
public class ProofController {
   /**
    * The program entry point.
    * @param args The start parameters.
    */
    @RequestMapping(value = "/**/{className}.java", method = RequestMethod.GET)
    @ResponseBody
   public ResponseEntity<ProofResult> proveSpec(@PathVariable String className, HttpServletRequest request) {
      // Get the file path for the request resource
      String path = ((String) request.getAttribute( HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE )).substring(7);
      ProofResult results = new ProofResult();
      File location = new File("projects/" + path); // Path to the source code folder/file or to a *.proof file
      List<File> classPaths = null; // Optionally: Additional specifications for API classes
      File bootClassPath = null; // Optionally: Different default specifications for Java API
      List<File> includes = null; // Optionally: Additional includes to consider
      if (location.exists()) {
        try {
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
           KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath, includes); // env.getLoadedProof() returns performed proof if a *.proof file is loaded
           try {
              // List all specifications of the selected type in the source location
              final List<Contract> proofContracts = new LinkedList<Contract>();
              KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(className);
              ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(keyType);
              for (IObserverFunction target : targets) {
                 ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(keyType, target);
                 for (Contract contract : contracts) {
                    proofContracts.add(contract);
                 }
              }
              
              // Perform proofs
              for (Contract contract : proofContracts) {
                 Proof proof = null;
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
                    boolean closed = proof.openGoals().isEmpty();
                    if (closed) 
                        results.addSuccess("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is verified.");
                    else
                        results.addFail("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is still open.");
                 }
                 catch (ProofInputException e) {
                    results.addError("Something went wrong at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ".");
                    System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
                    e.printStackTrace();
                 }
                 finally {
                    if (proof != null) {
                       proof.dispose(); // Ensure always that all instances of Proof are disposed
                    }
                 }
              }
           }
           finally {
              env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
           }
        }
        catch (ProblemLoaderException e) {
           results.addError("Couldn't process all relevant information for verification with KeY.");
           System.out.println("Exception at '" + location + "':");
           e.printStackTrace();
        }
      }
      
      return new ResponseEntity<ProofResult>(results, HttpStatus.OK);
   }
}
