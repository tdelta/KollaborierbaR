package events;

public class ConsoleMessageEvent extends ConsoleEvent {

  private final String message;

  public ConsoleMessageEvent(final Object source, final String projectName, final String filePath, final String message){
    super(source,"ConsoleMessageEvent" , projectName, filePath);
    this.message = message;
  }

  public String getMessage(){
    return message;
  }

}
