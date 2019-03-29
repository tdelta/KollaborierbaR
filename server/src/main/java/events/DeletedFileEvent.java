package events;

import java.util.List;

/**
 * Indicates, that a file had been deleted.
 *
 * See base class {@link ProofEvent} for more information.
 */
public class DeletedFileEvent extends ProjectEvent {
  private final String filePath;
  private final List<String> deleted;

  public DeletedFileEvent(
      final Object source,
      final String projectName,
      final String filePath,
      final List<String> deleted) {
    super(source, "DeletedFileEvent", projectName);
    this.filePath = filePath;
    this.deleted = deleted;
  }

  public String getFilePath() {
    return filePath;
  }

  /**
   * @return The paths of all files and folders that got deleted relative to the servers root folder
   *     (the paths should start with projects/)
   */
  public List<String> getDeleted() {
    return deleted;
  }
}
