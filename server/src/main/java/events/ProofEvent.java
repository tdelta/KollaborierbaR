package events;

import org.springframework.context.ApplicationEvent;

/**
 * The {@link server.ProofController} communicates changes to its data to {@link
 * synchronization.ProofSyncController} by sending it instances of this class's subclasses.
 *
 * <p>It is also sent by {@link synchronization.ProofSyncController} to clients, to inform them
 * about the changes.
 *
 * <p>This class just contains data which describes, which proof obligation of which file of what
 * project is affected by a change. The subclasses encode, what kind of change happened, by
 * setting @{@link #eventType} to an appropriate value. Depending on the change, they might also
 * extend this Event with additional data.
 *
 * @author Anton Haubner {@literal <anton.haubner@outlook.de>}
 */
abstract class ProofEvent extends ApplicationEvent {
  /** String describing, what kind of change happened. */
  private final String eventType;
  /** Which project is affected by a change of proof data */
  private final String projectName;
  /** Which file in the project is affected by a change of proof data */
  private final String filePath;
  /** What proof obligation within the file is affected by a change of proof data */
  private final int obligationIdx;

  public ProofEvent(
      final Object source,
      final String eventType,
      final String projectName,
      final String filePath,
      final int obligationIdx) {
    super(source);
    this.eventType = eventType;
    this.projectName = projectName;
    this.filePath = filePath;
    this.obligationIdx = obligationIdx;
  }

  public String getEventType() {
    return eventType;
  }

  public String getProjectName() {
    return projectName;
  }

  public String getFilePath() {
    return filePath;
  }

  public int getObligationIdx() {
    return obligationIdx;
  }
}
