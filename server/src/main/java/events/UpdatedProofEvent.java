package events;

/**
 * Indicates, that a temporarily stored proof result has changed. See base class {@link ProofEvent}
 * for more information.
 */
public class UpdatedProofEvent extends ProofEvent {
  public UpdatedProofEvent(
      final Object source,
      final String projectName,
      final String filePath,
      final int obligationIdx) {
    super(source, "UpdatedProofEvent", projectName, filePath, obligationIdx);
  }
}
