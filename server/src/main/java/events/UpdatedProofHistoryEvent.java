package events;

public class UpdatedProofHistoryEvent extends ProofEvent {
  public UpdatedProofHistoryEvent(
      final Object source,
      final String projectName,
      final String filePath,
      final int obligationIdx) {
    super(source, "UpdatedProofHistoryEvent", projectName, filePath, obligationIdx);
  }
}
