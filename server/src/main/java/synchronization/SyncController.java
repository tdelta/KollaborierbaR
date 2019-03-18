package synchronization;

import java.security.Principal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.event.EventListener;
import org.springframework.messaging.handler.annotation.DestinationVariable;
import org.springframework.messaging.handler.annotation.Header;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.messaging.simp.annotation.SubscribeMapping;
import org.springframework.stereotype.Controller;
import org.springframework.web.socket.messaging.SessionDisconnectEvent;
import org.springframework.web.socket.messaging.SessionUnsubscribeEvent;
import org.springframework.web.util.UriUtils;

@Controller
public class SyncController<Content> {
  // ContentId -> Users
  private ConcurrentHashMap<String, List<Principal>> usersPerContent = new ConcurrentHashMap<>();

  // ContentId -> Content
  private ConcurrentHashMap<String, Content> contents = new ConcurrentHashMap<>();
  
  //// SubscriptionId@User -> ContentId
  private ConcurrentHashMap<String, String> contentPerSubscription = new ConcurrentHashMap<>();

  private void saveSubscription(
    final String simpSubscriptionId, final Principal user, final String contentId) {

    contentPerSubscription.put(simpSubscriptionId + "@" + user.getName(), contentId);
  }

  private void deleteSubscription(final String simpSubscriptionId, final Principal user) {
    contentPerSubscription.remove(simpSubscriptionId + "@" + user.getName());
  }

  private String getContentIdBySubscription( final String simpSubscriptionId, final Principal user) {
    return contentPerSubscription.get(simpSubscriptionId + "@" + user.getName());
  }

  protected Content handleSubscriptionHelper(
      final Principal user,
      @Header final String simpSubscriptionId,
      final String contentId,
      final Content defaultContent
  ) {
    System.out.println("User " + user.getName() + " subscribed for content " + contentId);

    final List<Principal> users = usersPerContent.getOrDefault(contentId, new ArrayList<>(1));

    if (!users.contains(user)) {
      System.out.println("SyncController: Someone registered for " + contentId);
      users.add(user);

      usersPerContent.put(contentId, users);
    }

    saveSubscription(simpSubscriptionId, user, contentId);

    final Content prevContent;

    if (defaultContent != null) {
      prevContent = contents.putIfAbsent(contentId, defaultContent);
    }

    else if (!contents.containsKey(contentId)) {
      prevContent = null;
    }

    else {
      prevContent = contents.get(contentId);
      contents.remove(contentId);
    }

    return prevContent == null?
      defaultContent : prevContent;
  }

  protected void handleUnsubscribeHelper(final SessionUnsubscribeEvent event) {
    final Principal user = event.getUser();
    final String simpSubscriptionId =
        event.getMessage().getHeaders().get("simpSubscriptionId", String.class);

    final String contentId = getContentIdBySubscription(simpSubscriptionId, user);
    if (contentId != null) {
      System.out.println(
          "Got unsubscribe from " + event.getUser().getName() + " for content id " + contentId);

      final List<Principal> users = usersPerContent.getOrDefault(contentId, new ArrayList<>(0));

      users.remove(user);
      System.out.println("Removed user " + user.getName() + " from content id " + contentId);

      if (users.isEmpty()) {
        System.out.println("Removed content " + contentId + ", since all users left.");
        usersPerContent.remove(contentId);
        contents.remove(contentId);
      }
    }

    deleteSubscription(simpSubscriptionId, user);
  }

  protected void handleDisconnectHelper(final SessionDisconnectEvent event) {
    final Principal user = event.getUser();
    System.out.println("Disconnect of user " + user.getName());

    // remove from all contents, if still present there
    final Set<String> keys = usersPerContent.keySet();
    for (final String contentId : keys) {
      final List<Principal> users = usersPerContent.getOrDefault(contentId, new ArrayList<>(0));

      if (users.contains(user)) {
        System.out.println("Removed user " + user.getName() + " from content " + contentId);
        users.remove(user);

        if (users.isEmpty()) {
          System.out.println("Removed content " + contentId + ", since all users left.");
          usersPerContent.remove(contentId);
          contents.remove(contentId);
        }
      }
    }

    deleteSubscription(event.getSessionId(), user);
  }

  protected void setContent(final String contentId, final Content content) {
    contents.put(contentId, content);
  }

  protected List<Principal> getUsersByContentId(final String contentId) {
    return usersPerContent.getOrDefault(contentId, new ArrayList<>(0));
  }
}
