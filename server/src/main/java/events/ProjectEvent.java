package events;

import org.springframework.context.ApplicationEvent;

/**
 * The {@link server.ProjectController} communicates changes to projects stored on the server to
 * {@link synchronization.ProjectSyncController} by sending it instances of this class's subclasses.
 *
 * <p>It is also sent by {@link synchronization.ProjectSyncController} to clients, to inform them
 * about the changes.
 *
 * <p>This class just contains data which describes, which project is affected by a change. The
 * subclasses encode, what kind of change happened, by setting @{@link #eventType} to an appropriate
 * value. Depending on the change, they might also extend this Event with additional data.
 */
class ProjectEvent extends ApplicationEvent {
  /** String describing, what kind of change happened. */
  private final String eventType;
  /** Which project is affected by a change */
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
