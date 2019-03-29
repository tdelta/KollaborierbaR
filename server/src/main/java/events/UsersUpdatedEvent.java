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
  private int ownId;

  public UsersUpdatedEvent(Object source, final String projectName, final List<User> users) {
    super(source, "UsersUpdatedEvent", projectName);
    this.users = users;
    ownId = -1;
  }

  /**
   * Should be set to the id of the user that receives this event so that he can identify his own name
   * @param the unique project ID of the user
   */
  public void setOwnId(int id) {
    ownId = id;
  }

  /**
   * @return unique project ID of the user
   */
  public int getOwnId() {
    return ownId;
  }

  /**
   * @return Information about the users connected to the project containing: - their name - unique
   *     id in their collaborative document
   */
  public List<User> getUsers() {
    return users;
  }
}
