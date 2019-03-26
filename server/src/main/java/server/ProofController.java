package server;

import events.UpdatedProofEvent;
import events.UpdatedProofHistoryEvent;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.servlet.http.HttpServletRequest;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.ApplicationEventPublisher;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.servlet.HandlerMapping;
import proofutil.KeYWrapper;
import proofutil.ObligationResult;
import proofutil.ProofResult;
import repository.File;
import repository.MethodContract;
import repository.ObligationService;

/**
 * Basic KeY stub, that tries to prove all contracts in a file
 *
 * @author Martin Hentschel, Jonas Belouadi
 */
@RestController
@CrossOrigin
@RequestMapping("/proof")
public class ProofController {
  // ProjectFilePath -> (ObligationId -> ObligationResult)
  private ConcurrentHashMap<String, HashMap<Integer, List<ObligationResult>>> obligationResults =
      new ConcurrentHashMap<>();

  @Autowired private ApplicationEventPublisher applicationEventPublisher;
  @Autowired private ObligationService obligationService;

  /** Prove all Proof Obligations in a .java file or by index if a index is provided */
  @RequestMapping(value = "/**/{className}.java", method = RequestMethod.GET)
  @ResponseBody
  public ResponseEntity<ProofResult> proveAll(
      @PathVariable final String className,
      @RequestParam("obligationIdxs") final Optional<List<Integer>> obligationIdxs,
      final HttpServletRequest request) {
    // Get the file path for the request resource
    final String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(7);
    final KeYWrapper key = new KeYWrapper(path);
    // prove by index if index is present. ternary operator can be replaced with ifPresentOrElse if
    // Java 9 is used or higher
    final ProofResult result =
        obligationIdxs.isPresent()
            ? key.proveContractByIdxs(className, obligationIdxs.get())
            : key.proveAllContracts(className);
    key.dispose();

    return new ResponseEntity<ProofResult>(result, HttpStatus.OK);
  }

  @RequestMapping(value = "/**/{className}.java/obligation", method = RequestMethod.GET)
  public Set<Integer> listSavedObligations(
      @PathVariable final String className, final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    final File file = obligationService.getFile(projectFilePath);
    return file.getObligations().keySet();
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/last",
      method = RequestMethod.POST)
  public void uploadCurrentObligationResult(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request,
      @RequestBody ObligationResult obligationResult) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    System.out.println(
        "ProofController: Got obligation result for path "
            + projectFilePath
            + ": "
            + obligationResult.getResultMsg());

    File file = obligationService.getFile(projectFilePath);
    MethodContract methodContract = obligationService.getMethodContract(file, obligationIdx);
    System.out.println("Target name: " + obligationResult.getTargetName());

    obligationResult = obligationService.save(obligationResult);
    methodContract.setLast(obligationResult);
    obligationService.save(methodContract);

    final UpdatedProofEvent event =
        new UpdatedProofEvent(this, pathData.projectName, pathData.filePath, pathData.obligationId);
    applicationEventPublisher.publishEvent(event);
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/last",
      method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getCurrentProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    File file = obligationService.getFile(projectFilePath);
    if (file.getObligations().containsKey(obligationIdx)) {
      return new ResponseEntity<>(
          file.getObligations().get(obligationIdx).getLast(), HttpStatus.OK);
    }

    return new ResponseEntity<>(HttpStatus.BAD_REQUEST);
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history/{historyIdx}",
      method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getHistoricProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @PathVariable final int historyIdx,
      final HttpServletRequest request) {

    Optional<ObligationResult> requested = obligationService.findObligationResultById(historyIdx);
    if (requested.isPresent()) {
      return new ResponseEntity<>(requested.get(), HttpStatus.OK);
    }

    return new ResponseEntity<>(HttpStatus.BAD_REQUEST);
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history",
      method = RequestMethod.GET)
  public List<Long> getHistoryItems(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    final List<Long> ids = new LinkedList<>();

    final File file = obligationService.getFile(projectFilePath);
    if (file.getObligations().containsKey(obligationIdx)) {
      List<ObligationResult> history = file.getObligations().get(obligationIdx).getHistory();
      for (ObligationResult result : history) {
        ids.add(result.getId());
      }
    }

    return ids;
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history",
      method = RequestMethod.POST)
  public void addToHistory(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @RequestBody ObligationResult obligationResult,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    System.out.println("ProofController: About to save a new obligation result to history");

    final File file = obligationService.getFile(pathData.projectFilePath);
    final MethodContract methodContract = obligationService.getMethodContract(file, obligationIdx);

    obligationResult = obligationService.save(obligationResult);
    methodContract.addToHistory(obligationResult);
    obligationService.save(methodContract);

    final UpdatedProofHistoryEvent event =
        new UpdatedProofHistoryEvent(
            this, pathData.projectName, pathData.filePath, pathData.obligationId);
    System.out.println(
        "ProofController: Publising updated history. There are now "
            + methodContract.getHistory().size()
            + " results stored in the history of obligation "
            + obligationIdx);

    applicationEventPublisher.publishEvent(event);
  }

  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history/{historyIdx}",
      method = RequestMethod.DELETE)
  public ResponseEntity deleteFromHistory(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @PathVariable final int historyIdx,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    System.out.println(
        "ProofController: About to delete obligation result for "
            + projectFilePath
            + " on obligation id "
            + obligationIdx
            + " from history");

    File file = obligationService.getFile(projectFilePath);
    MethodContract methodContract = obligationService.getMethodContract(file, obligationIdx);
    if (methodContract.getHistory().size() >= historyIdx) {
      ObligationResult toDelete = methodContract.getHistory().get(historyIdx - 1);
      obligationService.deleteObligationResult(toDelete.getId());

      final UpdatedProofHistoryEvent event =
          new UpdatedProofHistoryEvent(
              this, pathData.projectName, pathData.filePath, pathData.obligationId);
      System.out.println(
          "ProofController: Publising updated history after removal of item " + historyIdx + ".");

      applicationEventPublisher.publishEvent(event);

      return new ResponseEntity(HttpStatus.OK);
    }

    return new ResponseEntity(HttpStatus.NOT_FOUND);
  }

  private static class PathData {
    public final int obligationId;
    public final String projectName;
    public final String filePath;
    public final String projectFilePath;

    public PathData(
        final int obligationId,
        final String projectName,
        final String filePath,
        final String projectFilePath) {
      this.obligationId = obligationId;
      this.projectName = projectName;
      this.filePath = filePath;
      this.projectFilePath = projectFilePath;
    }
  }

  private static PathData decodePath(final HttpServletRequest request) {
    final String regex =
        "\\/proof\\/(?<ProjectName>[^\\/]+)\\/(?<Path>.+)\\/obligation(\\/(?<ObligationId>\\d+)\\/.+)?";

    final String input =
        (String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE);
    System.out.println("ProofController: Prefix: " + input.substring(7));
    System.out.println("ProofController: Matching " + input);

    final Pattern p = Pattern.compile(regex);
    final Matcher m = p.matcher(input);

    System.out.println("ProofController: Matches: " + m.matches());

    final String projectName = m.group("ProjectName");
    System.out.println("ProofController: projectName " + projectName);

    final String path = m.group("Path");
    System.out.println("ProofController: path " + path);

    int obligationId = -1;
    try {
      obligationId = Integer.parseInt(m.group("ObligationId"));
    } catch (final Exception e) {
      obligationId = -1;
      System.out.println(
          "ProofController: Could not identify obligation id. Might have been ommited to access ../obligation and is no error in that case.");
    }

    System.out.println("ProofController: obligationId " + obligationId);

    final String projectFilePath = projectName + "/" + path;
    System.out.println("ProofController: projectFilePath: " + projectFilePath);

    return new PathData(obligationId, projectName, path, projectFilePath);
  }
}
