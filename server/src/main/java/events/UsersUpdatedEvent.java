package events;

import java.util.List;
import synchronization.User;

/**
 * Spring event that can be observed in an EventListener annotated method. {@link
 * org.springframework.context.event}
 *
 * <p>It is emmited when a user connects to a project or opens a collaborative document
 *
 * <p>It is sent to the client to pass on meto information about other users
 */
public class UsersUpdatedEvent extends ProjectEvent {

  private List<User> users;

  public UsersUpdatedEvent(Object source, final String projectName, final List<User> users) {
    super(source, "UsersUpdatedEvent", projectName);
    this.users = users;
  }

  /**
   * @return Information about the users connected to the project containing: - their name - unique
   *     id in their collaborative document
   */
  public List<User> getUsers() {
    return users;
  }
}
