package events;

public class UpdatedProofEvent extends ProofEvent {
  public UpdatedProofEvent(
      final Object source,
      final String projectName,
      final String filePath,
      final int obligationIdx) {
    super(source, "UpdatedProofEvent", projectName, filePath, obligationIdx);
  }
}