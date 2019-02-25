package synchronization;

import java.security.Principal;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.springframework.stereotype.Component;

@Component
public class UserList {

  // User names are constructed from an adjective and an animal
  // Animal names  correspond to names of fontawesome icons
  private String[] animals = new String[] {"cat", "crow", "dog", "dove", "dragon", "fish", "frog", "hippo", "horse", "kiwi", "otter", "spider"};

  private String[] adjectives = new String[] {"Wild", "Wise", "Drunk", "Fat"};

  // Maps Principal Object (Users managed by Stomp) to information about the users
  private ConcurrentHashMap<Principal, User> map = new ConcurrentHashMap<Principal, User>();

  /**
   * Creates a User object containing a generated name and saves it.
   * @param user The Stomp user
   */
  public void addUser(Principal user) {
    int animalId = (int) Math.floor(Math.random() * animals.length);
    int adjectiveId = (int) Math.floor(Math.random() * adjectives.length);

    map.put(user, new User(adjectives[adjectiveId], animals[animalId], -1));
  }

  /**
   * Sets the Crdt id of an existing user
   * @param user The Stomp user
   * @param id The Crdt id
   */
  public void setId(Principal user, int id) {
    User userName = map.get(user);
    if (userName != null) {
      userName.setCrdtId(id);
    }
  }

  /**
   * Returns a map of Stomp users to their additional Information
   * @return The map
   */
  public Set<ConcurrentHashMap.Entry<Principal, User>> entrySet() {
    return map.entrySet();
  }
}
