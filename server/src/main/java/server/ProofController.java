package server;

import java.util.Optional;
import javax.servlet.http.HttpServletRequest;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.servlet.HandlerMapping;
import proofutil.KeYWrapper;
import proofutil.ProofResult;

/**
 * Basic KeY stub, that tries to prove all contracts in a file
 *
 * @author Martin Hentschel, Jonas Belouadi
 */
@RestController
@CrossOrigin
@RequestMapping("/proof")
public class ProofController {
  /** Prove all Proof Obligations in a .java file or by index if a index is provided */
  @RequestMapping(value = "/**/{className}.java", method = RequestMethod.GET)
  @ResponseBody
  public ResponseEntity<ProofResult> proveAll(
      @PathVariable final String className,
      @RequestParam("obligationIdx") final Optional<Integer> obligationIdx,
      final HttpServletRequest request) {
    // Get the file path for the request resource
    final String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(7);
    final KeYWrapper key = new KeYWrapper(path);
    // prove by index if index is present. ternary operator can be replaced with ifPresentOrElse if
    // Java 9 is used or higher
    final ProofResult result =
        obligationIdx.isPresent()
            ? key.proveContractByIndex(className, obligationIdx.get())
            : key.proveAllContracts(className);
    key.dispose();

    return new ResponseEntity<ProofResult>(result, HttpStatus.OK);
  }
}
