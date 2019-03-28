package events;

/**
 * Indicates, that the proof result history of a proof obligation changed. This can for example
 * include new or deleted history items.
 *
 * <p>See base class {@link ProofEvent} for more information.
 */
public class UpdatedProofHistoryEvent extends ProofEvent {
  public UpdatedProofHistoryEvent(
      final Object source,
      final String projectName,
      final String filePath,
      final int obligationIdx) {
    super(source, "UpdatedProofHistoryEvent", projectName, filePath, obligationIdx);
  }
}
