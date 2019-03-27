package server;

import events.UpdatedProofEvent;
import events.UpdatedProofHistoryEvent;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
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

/**
 * Controller which provides access to KollaborierbaRs KeY functionalities. Those are:
 *
 * <p>- Running proofs on a file stored on the server - Temporarily storing proofs, such that other
 * clients working on the same file can access them - Permanently storing a history of proof results
 * for a proof obligation for each file This is utilized by the client, such that users can retrieve
 * and review proofs at a later time.
 *
 * @author Jonas Belouadi
 * @author Anton Haubner {@literal <anton.haubner@outlook.de>}
 */
@RestController
@CrossOrigin
@RequestMapping("/proof")
public class ProofController {
  // ProjectFilePath -> (ObligationId -> ObligationResult)
  private ConcurrentHashMap<String, HashMap<Integer, List<ObligationResult>>> obligationResults =
      new ConcurrentHashMap<>();

  /**
   * Required, to send events between Spring controllers.
   *
   * <p>In this class, it is used to inform {@link synchronization.ProofSyncController} about
   * changes to the proof result history and temporarily stored proof results.
   */
  @Autowired private ApplicationEventPublisher applicationEventPublisher;
  @Autowired private FileService fileService;

  /**
   * Try to prove all proof obligations in a .java file or by index if an index is provided
   *
   * @param className class name of the file in which the proofs shall be run
   * @param obligationIdxs the indices of the obligations to prove. Counted from top to bottom in
   *     the corresponding Java source file
   * @param macro the path to the macro file to use for the proof, if present
   * @return the proof results
   */
  @RequestMapping(value = "/**/{className}.java", method = RequestMethod.GET)
  @ResponseBody
  public ResponseEntity<ProofResult> runProof(
      @PathVariable final String className,
      @RequestParam("obligationIdxs") final Optional<List<Integer>> obligationIdxs,
      @RequestParam("macro") final Optional<String> macro,
      final HttpServletRequest request) {
    // Get the file path for the request resource
    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    final KeYWrapper key = new KeYWrapper(projectFilePath);

    // KeYWrapper provides KeY functionalities to this API controller
    Optional<String> macroContentsOptional = Optional.empty();

    if (macro.isPresent()) {
      // Read the macro file
      String macroContents = fileService.getCurrent(pathData.projectName + macro.get());
      if (macroContents != "") {
        macroContentsOptional = Optional.of(macroContents);
      }
    }

    // prove by index if index is present. ternary operator can be replaced with ifPresentOrElse if
    // Java 9 is used or higher
    final ProofResult result =
        obligationIdxs.isPresent()
            ? key.proveContractByIdxs(className, obligationIdxs.get(), macroContentsOptional)
            : key.proveAllContracts(className, macroContentsOptional);

    key.dispose();
    return new ResponseEntity<ProofResult>(result, HttpStatus.OK);
  }

  /**
   * Lists all obligation indices for the given file, for which there are saved proofs available on
   * the server.
   *
   * <p>The returned indices can be used to retrieve saved proofs using for example {@link
   * #getCurrentProof} or {@link getHistoricProof}.
   *
   * @param className Name of the class, for which we want to list obligation indices of saved
   *     proofs.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return indices of saved proof results, counted per file from top to bottom.
   */
  @RequestMapping(value = "/**/{className}.java/obligation", method = RequestMethod.GET)
  public List<Integer> listSavedObligations(
      @PathVariable final String className, final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    return new ArrayList<>(
        obligationResults.getOrDefault(projectFilePath, new HashMap<>()).keySet());
  }

  /**
   * Temporarily store the latest prove result for a proof. It is lost as soon as the server is shut
   * down.
   *
   * <p>This feature is used by KollaborierbaR to always share the latest proof result by any
   * developer with everyone working on the same file. Using this route, such a temporarily result
   * can be uploaded.
   *
   * <p>This method will inform {@link synchronization.ProofSyncController} about the change.
   *
   * @param className Name of the class, for which we want to save a temporary proof result.
   * @param obligationIdx Index of the proof obligation to which the uploaded result belongs,
   *     counted from top to bottom in the given Java file.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @param obligationResult Proof result to be stored.
   */
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

    final HashMap<Integer, List<ObligationResult>> prevObligations =
        obligationResults.getOrDefault(projectFilePath, new HashMap<>());

    final List<ObligationResult> prevResults =
        prevObligations.getOrDefault(obligationIdx, new LinkedList<>());

    if (prevResults.isEmpty()) {
      prevResults.add(0, obligationResult);
    } else {
      prevResults.set(0, obligationResult);
    }

    prevObligations.put(obligationIdx, prevResults);

    obligationResults.put(projectFilePath, prevObligations);

    final UpdatedProofEvent event =
        new UpdatedProofEvent(this, pathData.projectName, pathData.filePath, pathData.obligationId);
    applicationEventPublisher.publishEvent(event);
  }

  /**
   * Retrieves the temporary proof result stored by {@link #uploadCurrentObligationResult}.
   *
   * @param className Name of the class, for which we want to retrieve a temporary proof result.
   * @param obligationIdx Index of the proof obligation for which the latest temporary results shall
   *     be retrieved, counted from top to bottom in the given Java file.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return Temporarily stored proof result, or a NOT_FOUND (404) response, if there is no such
   *     result stored.
   */
  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/last",
      method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getCurrentProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    return retrieveObligationResult(projectFilePath, obligationIdx, 0)
        .map(obligationResult -> new ResponseEntity<>(obligationResult, HttpStatus.OK))
        .orElse(new ResponseEntity<>(HttpStatus.NOT_FOUND));
  }

  /**
   * Retrieves a proof result from the history. See class description for more information on the
   * proof history feature.
   *
   * @param className Name of the class, for which we want to retrieve a proof result from the
   *     history.
   * @param obligationIdx Index of the proof obligation for which the result shall be retrieved,
   *     counted from top to bottom in the given Java file.
   * @param historyIdx unique history id of the saved proof. See {@link #getHistoryItems} for more
   *     information about history ids.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return Saved proof result, or a NOT_FOUND (404) response, if there is no such result stored.
   */
  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history/{historyIdx}",
      method = RequestMethod.GET)
  public ResponseEntity<ObligationResult> getHistoricProof(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @PathVariable final int historyIdx,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    return retrieveObligationResult(projectFilePath, obligationIdx, historyIdx)
        .map(obligationResult -> new ResponseEntity<>(obligationResult, HttpStatus.OK))
        .orElse(new ResponseEntity<>(HttpStatus.NOT_FOUND));
  }

  /**
   * Retrieves a list of ids of all proof results stored in the history. See class description for
   * more information on the proof history feature.
   *
   * <p>These ids can be used to retrieve a saved proof result using {@link #getHistoricProof}.
   *
   * @param className Name of the class, for which we want to retrieve the list of ids
   * @param obligationIdx Index of the proof obligation for which the history ids shall be
   *     retrieved.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return List of ids of saved proof results. The history id of a saved result is an indicator of
   *     its age. Bigger ids mean the saved result is more recent. So sorting them by descending
   *     order sorts them in order of their age, beginning with the newest saved proofs.
   */
  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history",
      method = RequestMethod.GET)
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

  /**
   * Adds a proof result to the history of saved results. See class description for more information
   * on the proof history feature.
   *
   * <p>This method will inform {@link synchronization.ProofSyncController} about the changed
   * history.
   *
   * @param className Name of the class, for which we want to save a result
   * @param obligationIdx Index of the proof obligation for which a proof result shall be saved.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return history id of the saved proof, see {@link #getHistoryItems} for more information on
   *     these ids.
   */
  @RequestMapping(
      value = "/**/{className}.java/obligation/{obligationIdx}/history",
      method = RequestMethod.POST)
  public int addToHistory(
      @PathVariable final String className,
      @PathVariable final int obligationIdx,
      @RequestBody ObligationResult obligationResult,
      final HttpServletRequest request) {

    final PathData pathData = decodePath(request);
    final String projectFilePath = pathData.projectFilePath;

    final int newHistoryIdx = 1;

    System.out.println("ProofController: About to save a new obligation result to history");

    final HashMap<Integer, List<ObligationResult>> previousObligations =
        obligationResults.getOrDefault(projectFilePath, new HashMap<>());

    System.out.println(
        "ProofController: There is data for " + previousObligations.size() + " obligations.");

    final List<ObligationResult> obligationResultHistory =
        previousObligations.getOrDefault(obligationIdx, new LinkedList<>());

    System.out.println(
        "ProofController: Updating history. There are "
            + (obligationResultHistory.size() - 1)
            + " results stored in the history of obligation "
            + obligationIdx
            + " before modifying it.");

    if (obligationResultHistory.isEmpty()) {
      System.out.println(
          "ProofController: There isnt any proof saved yet for obligation "
              + obligationIdx
              + ", so we will not only save the submitted obligation result to history, but also store it as the last proof.");

      obligationResultHistory.add(0, obligationResult);
    }

    obligationResultHistory.add(newHistoryIdx, obligationResult);
    previousObligations.put(obligationIdx, obligationResultHistory);

    obligationResults.put(projectFilePath, previousObligations);

    final UpdatedProofHistoryEvent event =
        new UpdatedProofHistoryEvent(
            this, pathData.projectName, pathData.filePath, pathData.obligationId);
    System.out.println(
        "ProofController: Publising updated history. There are now "
            + (obligationResultHistory.size() - 1)
            + " results stored in the history of obligation "
            + obligationIdx);

    applicationEventPublisher.publishEvent(event);

    return newHistoryIdx;
  }

  /**
   * Deletes a proof result from the history of saved results. See class description for more
   * information on the proof history feature.
   *
   * <p>This method will inform {@link synchronization.ProofSyncController} about the change.
   *
   * @param className Name of the class, for which we want to delete a result
   * @param obligationIdx Index of the proof obligation for which a proof result shall be deleted.
   * @param historyIdx unique history id of the result which shall be deleted. See {@link
   *     #getHistoryItems} for more information about history ids.
   * @param request Object describing the HTTP request, which triggered this method. Filled in by
   *     Spring.
   * @return history id of the result to be deleted, see {@link #getHistoryItems} for more
   *     information on these ids. If there is no result matching the parameters, NOT_FOUND (404)
   *     will be returned.
   */
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

    final int newHistoryIdx = 1;

    System.out.println(
        "ProofController: About to delete obligation result for "
            + projectFilePath
            + " on obligation id "
            + obligationIdx
            + " from history");

    final HashMap<Integer, List<ObligationResult>> previousObligations =
        obligationResults.getOrDefault(projectFilePath, new HashMap<>());

    final List<ObligationResult> obligationResultHistory =
        previousObligations.getOrDefault(obligationIdx, new LinkedList<>());

    if (historyIdx == 0) {
      System.out.println(
          "ProofController: Cant delete last element using the history delete method.");

      return new ResponseEntity(HttpStatus.NOT_FOUND);
    } else if (historyIdx < obligationResultHistory.size()) {
      obligationResultHistory.remove(historyIdx);

      previousObligations.put(obligationIdx, obligationResultHistory);
      obligationResults.put(projectFilePath, previousObligations);

      final UpdatedProofHistoryEvent event =
          new UpdatedProofHistoryEvent(
              this, pathData.projectName, pathData.filePath, pathData.obligationId);
      System.out.println(
          "ProofController: Publising updated history after removal of item " + historyIdx + ".");

      applicationEventPublisher.publishEvent(event);

      return new ResponseEntity(HttpStatus.OK);
    } else {
      System.out.println("ProofController: Cant delete history element out of bounds.");

      return new ResponseEntity(HttpStatus.NOT_FOUND);
    }
  }

  /**
   * Helper method for loading a proof result saved to history. See class description for more
   * information on the proof history feature.
   *
   * @param projectFilePath path to a Java source file, for which a result shall be retrieved. It
   *     includes the project name as the root folder.
   * @param obligationId Index of the proof obligation for which a proof result shall be retrieved.
   * @param historyIdx unique history id of the result which shall be retrieved. See {@link
   *     #getHistoryItems} for more information about history ids.
   * @return A proof result, if one had been saved for the given parameters. Nothing otherwise.
   */
  private Optional<ObligationResult> retrieveObligationResult(
      final String projectFilePath, final int obligationId, final int historyIdx) {
    final List<ObligationResult> obligationResultHistory =
        this.obligationResults
            .getOrDefault(projectFilePath, new HashMap<>())
            .getOrDefault(obligationId, new LinkedList<>());

    final Optional<ObligationResult> maybeObligationResult;
    if (obligationResultHistory != null && !obligationResultHistory.isEmpty()) {
      final ObligationResult obligationResult = obligationResultHistory.get(historyIdx);

      System.out.println(
          "ProofController: Returning obligation result for "
              + projectFilePath
              + ": "
              + obligationResult.getResultMsg());

      maybeObligationResult = Optional.of(obligationResult);
    } else {
      System.out.println(
          "ProofController: Could not retrieve obligation result, since there is no result saved with id "
              + projectFilePath
              + " and "
              + " history number "
              + historyIdx);

      maybeObligationResult = Optional.empty();
    }

    return maybeObligationResult;
  }

  /**
   * Since Spring does not decode arbitrary paths (`/**`) into method parameters for us, we have to
   * extract them from the request object.
   *
   * <p>This method just provides a basic extraction of the whole path without any further
   * processing. See {@link #decodePath} for a similiar method, which provides more information on
   * the contents of the path.
   *
   * @param request Spring generated object, describing a request. Can be obtained by simply adding
   *     the type to the parameter list of a method with a {@link RequestMapping}.
   * @return The full path used in {@code request}, with the leading `/proof/` part removed.
   */
  private static String extractPath(final HttpServletRequest request) {
    return ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
        .substring(7); // remove `/proof/` from the start of the path.
  }

  /**
   * Simple data structure utilized by {@link #decodePath} to provide information extracted from a
   * request path.
   */
  private static class PathData {
    /**
     * Index of a proof obligation, as counted from top to bottom in its Java source file.
     *
     * <p>It may be set to {@code -1}, if there was no obligation index specified within the path.
     */
    public final int obligationId;
    /** Name of the project referenced in the request path. */
    public final String projectName;
    /** Path to a file within the project */
    public final String filePath;
    /** {@link projectName} and {@link filePath} concatenated with an `/` */
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

  /**
   * Since Spring does not decode arbitrary paths (`/**`) into method parameters for us, we have to
   * extract them from the request object.
   *
   * <p>It also extracts additional information from the path.
   * See {@link PathData} for the extracted information.
   *
   * @param request Spring generated object, describing a request. Can be obtained by simply adding
   *     the type to the parameter list of a method with a {@link RequestMapping}.
   * @return The full path used in {@code request}, with the leading `/proof/` part removed.
   */
  private static PathData decodePath(final HttpServletRequest request) {
    // regex, which is used to extract information from the request path by
    // defining groups
    final String regex =
        "\\/proof\\/(?<ProjectName>[^\\/]+)\\/(?<Path>[^\\.]+\\.java)(\\/obligation(\\/(?<ObligationId>\\d+)\\/.+)?)?";

    // Retrieving the request path from the request object
    final String input =
        (String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE);

    // Applying the regex
    final Pattern p = Pattern.compile(regex);
    final Matcher m = p.matcher(input);
    m.matches();

    // Extracting information
    final String projectName = m.group("ProjectName");
    final String path = m.group("Path");

    // If there was no obligation id specified in the path, set it to -1
    int obligationId = -1;
    try {
      obligationId = Integer.parseInt(m.group("ObligationId"));
    } catch (final Exception e) {
      obligationId = -1;
      System.out.println(
          "ProofController: Could not identify obligation id. Might have been ommited to access ../obligation and is no error in that case.");
    }

    final String projectFilePath = projectName + "/" + path;

    return new PathData(obligationId, projectName, path, projectFilePath);
  }
}
