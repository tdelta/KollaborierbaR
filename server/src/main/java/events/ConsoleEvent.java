package events;

import org.springframework.context.ApplicationEvent;

public class ConsoleEvent extends ApplicationEvent{

  private final String eventType;

  private final String projectName;

  private final String filePath;

  public ConsoleEvent(final Object source, final String eventType, final String projectName, final String filePath){
    super(source);
    this.projectName = projectName;
    this.filePath = filePath;
    this.eventType = eventType;
  }

  public String getProjectName(){
    return projectName;
  }

  public String getFilePath(){
    return filePath;
  }

  public String getEventType(){
    return eventType;
  }

}
