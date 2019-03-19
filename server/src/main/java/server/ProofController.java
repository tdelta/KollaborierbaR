package server;

import java.util.regex.Pattern;
import java.util.regex.Matcher;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.HashMap;
import javax.servlet.http.HttpServletRequest;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.servlet.HandlerMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.context.ApplicationEventPublisher;

import proofutil.KeYWrapper;
import proofutil.ProofResult;
import proofutil.ProofNode;
import proofutil.ObligationResult;

import events.UpdatedProofEvent;
import events.UpdatedProofHistoryEvent;

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
  private ConcurrentHashMap<String, HashMap<Integer, List<ObligationResult>>> obligationResults = new ConcurrentHashMap<>();

  @Autowired private ApplicationEventPublisher applicationEventPublisher;

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
  public List<Integer> listSavedObligations(
      @PathVariable final String className,
      final HttpServletRequest request) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      return new ArrayList<>(
          obligationResults
            .getOrDefault(projectFilePath, new HashMap<>())
            .keySet()
          );
  }

  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/last", method = RequestMethod.POST)
  public void uploadCurrentObligationResult(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request,
      @RequestBody ObligationResult obligationResult) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      System.out.println("ProofController: Got obligation result for path " + projectFilePath + ": " + obligationResult.getResultMsg());

      final HashMap<Integer, List<ObligationResult>> prevObligations = obligationResults
        .getOrDefault(projectFilePath, new HashMap<>());

      final List<ObligationResult> prevResults = prevObligations
        .getOrDefault(obligationIdx, new LinkedList<>());

      prevResults.add(0, obligationResult);
      prevObligations.put(obligationIdx, prevResults);

      obligationResults.put(projectFilePath, prevObligations);

      final UpdatedProofEvent event = new UpdatedProofEvent(
          this,
          pathData.projectName,
          pathData.filePath,
          pathData.obligationId
      );
      applicationEventPublisher.publishEvent(event);
  }

  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/last", method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getCurrentProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request) {
      
      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      return
        retrieveObligationResult(projectFilePath, obligationIdx, 0)
          .map(obligationResult -> new ResponseEntity<>(obligationResult, HttpStatus.OK))
          .orElse(new ResponseEntity<>(HttpStatus.BAD_REQUEST));
  }

  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/history/{historyIdx}", method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getHistoricProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @PathVariable final int historyIdx,
      final HttpServletRequest request) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      return
        retrieveObligationResult(projectFilePath, obligationIdx, historyIdx)
          .map(obligationResult -> new ResponseEntity<>(obligationResult, HttpStatus.OK))
          .orElse(new ResponseEntity<>(HttpStatus.BAD_REQUEST));
  }
  
  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/history", method = RequestMethod.GET)
  public List<Integer> getHistoryItems(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;
      final List<ObligationResult> prevResults =
        obligationResults
          .getOrDefault(projectFilePath, new HashMap<>())
          .getOrDefault(obligationIdx, new LinkedList<>());

      final List<Integer> result = new LinkedList<>();
      for (int i = 1; i < prevResults.size(); ++i) {
        result.add(i);
      }

      return result;
  }

  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/history", method = RequestMethod.POST)
  public int addToHistory(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @RequestBody ObligationResult obligationResult,
      final HttpServletRequest request) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      final int newHistoryIdx = 1;

      System.out.println("ProofController: About to save a new obligation result to history");

      final HashMap<Integer, List<ObligationResult>> previousObligations = obligationResults.getOrDefault(projectFilePath, new HashMap<>());

      System.out.println("ProofController: There is data for " + previousObligations.size() + " obligations.");

      final List<ObligationResult> obligationResultHistory = previousObligations.getOrDefault(obligationIdx, new LinkedList<>());
      if (obligationResultHistory.isEmpty()) {
        System.out.println("ProofController: There isnt any proof saved yet for obligation " + obligationIdx + ", so we will not only save the submitted obligation result to history, but also store it as the last proof.");

        obligationResultHistory.add(0, obligationResult);
      }
      obligationResultHistory.add(newHistoryIdx, obligationResult);
      previousObligations.put(obligationIdx, obligationResultHistory);

      obligationResults.put(projectFilePath, previousObligations);

      final UpdatedProofHistoryEvent event = new UpdatedProofHistoryEvent(
          this,
          pathData.projectName,
          pathData.filePath,
          pathData.obligationId
      );
      System.out.println("ProofController: Publising updated history. There are now " + (obligationResultHistory.size()-1) + " results stored in the history of obligation " + obligationIdx);

      applicationEventPublisher.publishEvent(event);

      return newHistoryIdx;
  }

  @RequestMapping(value = "/**/{className}.java/obligation/{obligationIdx}/history/{historyIdx}", method = RequestMethod.DELETE)
  public ResponseEntity deleteFromHistory(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @PathVariable final int historyIdx,
      final HttpServletRequest request) {

      final PathData pathData = decodePath(request);
      final String projectFilePath = pathData.projectFilePath;

      final int newHistoryIdx = 1;

      System.out.println("ProofController: About to delete obligation result for " + projectFilePath + " on obligation id " + obligationIdx + " from history");

      final HashMap<Integer, List<ObligationResult>> previousObligations = obligationResults.getOrDefault(projectFilePath, new HashMap<>());

      final List<ObligationResult> obligationResultHistory = previousObligations.getOrDefault(obligationIdx, new LinkedList<>());

      if (historyIdx == 0) {
        System.out.println("ProofController: Cant delete last element using the history delete method.");

        return new ResponseEntity(HttpStatus.BAD_REQUEST);
      }

      else if (historyIdx < obligationResultHistory.size()) {
        obligationResultHistory.remove(historyIdx);

        previousObligations.put(obligationIdx, obligationResultHistory);
        obligationResults.put(projectFilePath, previousObligations);

        final UpdatedProofHistoryEvent event = new UpdatedProofHistoryEvent(
            this,
            pathData.projectName,
            pathData.filePath,
            pathData.obligationId
        );
        System.out.println("ProofController: Publising updated history after removal of item " + historyIdx + ".");

        applicationEventPublisher.publishEvent(event);

        return new ResponseEntity(HttpStatus.OK);
      }

      else {
        System.out.println("ProofController: Cant delete history element out of bounds.");

        return new ResponseEntity(HttpStatus.BAD_REQUEST);
      }
  }

  private Optional<ObligationResult> retrieveObligationResult(final String projectFilePath, final int obligationId, final int historyIdx) {
      final List<ObligationResult> obligationResultHistory = this
        .obligationResults
        .getOrDefault(projectFilePath, new HashMap<>())
        .getOrDefault(obligationId, new LinkedList<>());

      final Optional<ObligationResult> maybeObligationResult;
      if (obligationResultHistory != null && !obligationResultHistory.isEmpty()) {
        final ObligationResult obligationResult = obligationResultHistory.get(0);

        System.out.println("ProofController: Returning obligation result for " + projectFilePath + ": " + obligationResult.getResultMsg());

        maybeObligationResult = Optional.of(obligationResult);
      }

      else {
        System.out.println("ProofController: Could not retrieve obligation result, since there is no result saved with id " +  projectFilePath + " and " + " history number " + historyIdx);

        maybeObligationResult = Optional.empty();
      }

      return maybeObligationResult;
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
      final String projectFilePath
    ) {
      this.obligationId = obligationId;
      this.projectName = projectName;
      this.filePath = filePath;
      this.projectFilePath = projectFilePath;
    }
  }

  private static PathData decodePath(final HttpServletRequest request) {
      final String regex = "\\/proof\\/(?<ProjectName>[^\\/]+)\\/(?<Path>.+)\\/obligation(\\/(?<ObligationId>\\d+)\\/.+)?";

      final String input = (String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE);
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
      }

      catch(final Exception e) {
        obligationId = -1;
        System.out.println("ProofController: Could not identify obligation id. Might have been ommited to access ../obligation and is no error in that case.");
      }

      System.out.println("ProofController: obligationId " + obligationId);

      final String projectFilePath =  projectName + "/" + path;
      System.out.println("ProofController: projectFilePath: " + projectFilePath);

      return new PathData(
        obligationId,
        projectName,
        path,
        projectFilePath
      );
  }
}
