package events;

public class DeletedFileEvent extends ProjectEvent {
  private final String filePath;

  public DeletedFileEvent(final Object source, final String projectName, final String filePath) {
    super(source, "DeletedFileEvent", projectName);
    this.filePath = filePath;
  }

  public String getFilePath() {
    return filePath;
  }
}
