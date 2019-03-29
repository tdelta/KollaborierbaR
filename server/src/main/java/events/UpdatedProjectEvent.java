package events;

/**
 * Can indicate any change to a project structure and should trigger a project
 * structure reload on the client.
 *
 * Currently it is only used to inform clients about new files added to the
 * project.
 *
 * See base class {@link ProofEvent} for more information.
 */
public class UpdatedProjectEvent extends ProjectEvent {
  public UpdatedProjectEvent(final Object source, final String projectName) {
    super(source, "UpdatedProjectEvent", projectName);
  }
}
