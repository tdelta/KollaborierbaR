package synchronization;

import java.security.Principal;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.springframework.stereotype.Component;

/**
 * Autowireable component that is shared over websocket sessions.
 *
 * <p>Holds information about all users currently working on collaborative documents
 */
@Component
public class UserList {

  private String[] animals =
      new String[] {
        "cat", "crow", "dog", "dove", "dragon", "fish", "frog", "hippo", "horse", "kiwi", "otter",
        "spider"
      };

  private String[] adjectives = new String[] {"Wild", "Wise", "Drunk", "Fat", "Damned", "Lousy", "Sinister", "Mischievous", "Jealous", "Grumpy", "Greedy"};

  // Maps Principal Object (Users managed by Stomp) to information about the users
  private ConcurrentHashMap<Principal, User> map = new ConcurrentHashMap<Principal, User>();

  /**
   * Creates a User object containing a generated name and saves it.
   *
   * @param user The Stomp user
   */
  public void addUser(Principal user) {
    int animalId = (int) Math.floor(Math.random() * animals.length);
    int adjectiveId = (int) Math.floor(Math.random() * adjectives.length);

    map.put(user, new User(adjectives[adjectiveId], animals[animalId], -1, -1));
  }

  /**
   * Sets the id of the user, unique in the project that they are workin in
   *
   * @param user The Stomp user
   * @param usersInProject List of information about all users that are connected to a given project
   */
  public void setUniqueIdForProject(Principal user, List<User> usersInProject) {
    User userName = map.get(user);
    if (userName != null) {
      userName.setUniqueIdForProject(usersInProject);
    }
  }

  /**
   * Gets the id of the user, unique in the project that they are workin in
   *
   * @param user The Stomp user
   * @return return the user that belongs to the parameter
   */
  public int getUniqueIdForProject(Principal user) {
    User userName = map.get(user);
    if (userName != null)
      return userName.getIdInProject();
    return -1;
  }

  /**
   * Sets the Crdt id of an existing user
   *
   * @param user The Stomp user
   * @param id The Crdt id
   */
  public void setCrdtId(Principal user, int id) {
    User userName = map.get(user);
    if (userName != null) {
      userName.setCrdtId(id);
    }
  }

  /**
   * Returns a map of Stomp users to their additional Information
   *
   * @return The map
   */
  public Set<ConcurrentHashMap.Entry<Principal, User>> entrySet() {
    return map.entrySet();
  }

  /**
   * Given the identification of a user from a websocket request, returns saved information about
   * the user
   *
   * @return the information associated with the user
   */
  public User get(Principal user) {
    return map.get(user);
  }
}
