package events;

import java.util.List;

public class DeletedProjectEvent extends ProjectEvent {

  private final List<String> deleted;

  public DeletedProjectEvent(
      final Object source, final String projectName, final List<String> deleted) {
    super(source, "DeletedProjectEvent", projectName);
    this.deleted = deleted;
  }

  /**
   * @return The paths of all files and folders that got deleted relative to the servers root folder
   *     (the paths should start with projects/)
   */
  public List<String> getDeleted() {
    return deleted;
  }
}
