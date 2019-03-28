package repository;

import events.DeletedFileEvent;
import events.DeletedProjectEvent;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.event.EventListener;
import org.springframework.stereotype.Service;
import proofutil.ObligationResult;
import proofutil.OpenGoalInfo;

/**
 * Wrapper for the database interfaces that takes care of creating deleting and saving. Can be
 * autowired if needed.
 */
@Service
public class ObligationService {

  @Autowired private ObligationResultRepository obligationResultRepository;
  @Autowired private MethodContractRepository methodContractRepository;
  @Autowired private FileRepository fileRepository;
  @Autowired private OpenGoalInfoRepository openGoalInfoRepository;

  /** Callback for when a DeletedProjectEvent is triggered */
  @EventListener
  public void onProjectDeleted(final DeletedProjectEvent e) {
    deleteFiles(e.getDeleted());
  }

  /** Callback for when a DeletedFileEvent is triggered */
  @EventListener
  public void onFileDeleted(final DeletedFileEvent e) {
    deleteFiles(e.getDeleted());
  }

  /**
   * Purges files from the database. All Obligation results belonging to the file will be deleted as
   * well.
   *
   * @param paths Paths of the files to delete
   */
  public void deleteFiles(final List<String> paths) {
    for (String path : paths) {
      path = path.replaceFirst("projects/", "");
      System.out.println("Obligation Service: Delete file: " + path);
      if (fileRepository.existsByName(path)) {
        File toDelete = fileRepository.findByName(path);
        fileRepository.delete(toDelete);
      }
    }
  }

  /**
   * Creates a file with the given name and saves it in the database or returns it from the database
   * if it already exists.
   *
   * @param filename unique file name (should include the project name and filepath)
   */
  public File getFile(String filename) {
    System.out.println("ObligationService: Loading file: " + filename);
    if (!fileRepository.existsByName(filename)) {
      File file = new File(filename);
      file = fileRepository.save(file);
      return file;
    } else {
      return fileRepository.findByName(filename);
    }
  }

  /**
   * Creates a method contract in the proof history of a given file and saves it or returns it from
   * the database if it already exists
   *
   * @param file the file that the
   */
  public MethodContract getMethodContract(File file, int obligationId) {
    Map<Integer, MethodContract> contracts = file.getObligations();
    if (contracts.containsKey(obligationId)) {
      return contracts.get(obligationId);
    } else {
      MethodContract methodContract = new MethodContract(obligationId);
      methodContract = methodContractRepository.save(methodContract);
      methodContract.setFile(file);
      methodContract = methodContractRepository.save(methodContract);
      return methodContract;
    }
  }

  /**
   * Delete an obligation result from the database
   *
   * @param id primary key of the obligation result
   */
  public void deleteObligationResult(long id) {
    obligationResultRepository.deleteById(id);
  }

  /**
   * Load an obligation result from the database by its primary key
   *
   * @return an obligation result or Optional.empty() if no obligation result with the given id
   *     exists
   */
  public Optional<ObligationResult> findObligationResultById(long id) {
    return obligationResultRepository.findById(id);
  }

  /**
   * Save an obligation result including all variables in the database
   *
   * @return the saved obligation result with updated primary key
   */
  public ObligationResult save(ObligationResult obligationResult) {
    List<OpenGoalInfo> openGoals = obligationResult.getOpenGoals();
    if (openGoals != null) {
      // Save all objects referencing the obligation result before saving the obligation result
      openGoals.stream().map(openGoal -> openGoalInfoRepository.save(openGoal));
    }
    return obligationResultRepository.save(obligationResult);
  }

  /**
   * Save a method contract in the database, object variables must be saved seperately
   *
   * @param methodContract to save
   * @return the saved method contract with updated primary key
   */
  public MethodContract save(MethodContract methodContract) {
    return methodContractRepository.save(methodContract);
  }
}
