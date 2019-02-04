package events;

import org.springframework.context.ApplicationEvent;

class ProjectEvent extends ApplicationEvent {
  private final String eventType;
  private final String projectName;

  public ProjectEvent(final Object source, final String eventType, final String projectName) {
    super(source);
    this.eventType = eventType;
    this.projectName = projectName;
  }

  public String getEventType() {
    return eventType;
  }

  public String getProjectName() {
    return projectName;
  }
}
