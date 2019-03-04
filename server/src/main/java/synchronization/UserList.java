package synchronization;

import java.security.Principal;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.springframework.stereotype.Component;

@Component
public class UserList {

  private String[] animals =
      new String[] {
        "cat", "crow", "dog", "dove", "dragon", "fish", "frog", "hippo", "horse", "kiwi", "otter",
        "spider"
      };

  private String[] adjectives = new String[] {"Wild", "Wise", "Drunk", "Fat"};

  private ConcurrentHashMap<Principal, User> map = new ConcurrentHashMap<Principal, User>();

  public void addUser(Principal user) {
    int animalId = (int) Math.floor(Math.random() * animals.length);
    int adjectiveId = (int) Math.floor(Math.random() * adjectives.length);

    map.put(user, new User(adjectives[adjectiveId], animals[animalId], -1));
  }

  public void setId(Principal user, int id) {
    User userName = map.get(user);
    if (userName != null) {
      userName.setCrdtId(id);
    }
  }

  public Set<ConcurrentHashMap.Entry<Principal, User>> entrySet() {
    return map.entrySet();
  }

  public User get(Principal user) {
    return map.get(user);
  }
}
