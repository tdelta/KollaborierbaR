package events;

import java.util.List;
import synchronization.User;

public class UsersUpdatedEvent extends ProjectEvent {

  private List<User> users;

  public UsersUpdatedEvent(Object source, final String projectName, final List<User> users) {
    super(source, "UsersUpdatedEvent", projectName);
    this.users = users;
  }

  public List<User> getUsers() {
    return users;
  }
}
