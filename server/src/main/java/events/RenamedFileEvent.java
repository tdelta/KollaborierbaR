package events;

/**
 * Indicates, that a file had been renamed.
 *
 * See base class {@link ProofEvent} for more information.
 */
public class RenamedFileEvent extends ProjectEvent {
  private final String originalPath;
  private final String newPath;

  public RenamedFileEvent(
      final Object source,
      final String projectName,
      final String originalPath,
      final String newPath) {
    super(source, "RenamedFileEvent", projectName);

    this.originalPath = originalPath;
    this.newPath = newPath;
  }

  /**
   * Path of the renamed file, before it got renamed.
   */
  public String getOriginalPath() {
    return originalPath;
  }

  /**
   * Path of the renamed file, after renaming.
   */
  public String getNewPath() {
    return newPath;
  }
}
