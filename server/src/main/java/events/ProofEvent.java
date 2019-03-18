package events;

import org.springframework.context.ApplicationEvent;

abstract class ProofEvent extends ApplicationEvent {
  private final String eventType;
  private final String projectName;
  private final String filePath;
  private final int obligationIdx;

  public ProofEvent(final Object source, final String eventType, final String projectName, final String filePath, final int obligationIdx) {
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
