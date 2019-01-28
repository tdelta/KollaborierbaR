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
import proofutil.KeYWrapper;

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
      System.out.println("Pimmel");

      KeYWrapper key = new KeYWrapper(path);
      ProofResult result = key.proveAllContracts(className);
      key.dispose();

      return new ResponseEntity<ProofResult>(result, HttpStatus.OK);
   }
}
