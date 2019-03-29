package events;

public class ErrorEvent extends ConsoleEvent {

  private final String message;

  public ErrorEvent(
      final Object source, final String projectName, final String filePath, final String message) {
    super(source, "ErrorEvent", projectName, filePath);
    this.message = message;
  }

  public String getMessage() {
    return message;
  }
}
