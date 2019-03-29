package events;

/**
 * Indicates, that the content of a file changed.
 *
 * See base class {@link ProofEvent} for more information.
 */
public class UpdatedFileEvent extends ProjectEvent {
  private final String filePath;

  public UpdatedFileEvent(final Object source, final String projectName, final String filePath) {
    super(source, "UpdatedFileEvent", projectName);
    this.filePath = filePath;
  }

  /**
   * Path of the changed file.
   */
  public String getFilePath() {
    return filePath;
  }
}
