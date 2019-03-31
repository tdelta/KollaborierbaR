package synchronization;

import java.security.Principal;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.springframework.messaging.handler.annotation.Header;
import org.springframework.web.socket.messaging.SessionDisconnectEvent;
import org.springframework.web.socket.messaging.SessionUnsubscribeEvent;

/**
 * Generic helper class for managing STOMP subscriptions and associated data.
 *
 * <p>Controllers which implement STOMP destinations, clients can subscribe to via websocket
 * connections (see <a href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP
 * 1.2 specification</a>), should inherit from this class.
 *
 * <p>It provides them with methods to handle
 *
 * <p>1. Subscriptions (associating clients with a destination/topic, see {@link
 * #handleSubscriptionHelper} and {@link #getUsersByDestinationId}) 2. Unsubscribing and closed
 * connections (see {@link #handleUnsubscribeHelper} and {@link #handleDisconnectHelper}) 3. Storing
 * additional data per destination/topic (see {@link #setDestinationData})
 *
 * @author Anton Haubner {@literal <anton.haubner@outlook.de>}
 * @param <T> Type of additional data associated with each STOMP destination. Set it to {@code
 *     Void}, if you dont want to store addional data.
 */
public class SyncController<T> {
  /**
   * Associates a STOMP destination/topic with users subscribed to it. Mapping: DestinationId ->
   * Users
   */
  private ConcurrentHashMap<String, List<Principal>> usersPerDestination =
      new ConcurrentHashMap<>();

  /**
   * Associates a STOMP destination/topic with some additional data, see class description. Mapping:
   * DestinationId -> T
   */
  private ConcurrentHashMap<String, T> contents = new ConcurrentHashMap<>();

  /**
   * Associates an subscription id pared with a client with a destination/topic. Mapping:
   * SubscriptionId@User -> DestinationId
   */
  private ConcurrentHashMap<String, String> destinationPerSubscription = new ConcurrentHashMap<>();

  /**
   * Helper method, stores a new association, of a client and their subscription id to a
   * destination/topic.
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param user unique identifier for a client connected via websocket to the server.
   * @param destinationId unique identifier for a destination/topic
   */
  private void saveSubscription(
      final String simpSubscriptionId, final Principal user, final String destinationId) {

    destinationPerSubscription.put(simpSubscriptionId + "@" + user.getName(), destinationId);
  }

  /**
   * Helper method, removes a client from a destination/topic
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param user unique identifier for a client connected via websocket to the server.
   */
  private void deleteSubscription(final String simpSubscriptionId, final Principal user) {
    destinationPerSubscription.remove(simpSubscriptionId + "@" + user.getName());
  }

  /**
   * Helper method, retrieves the destination a user is subscribed to, associated with the given
   * STOMP subscription id.
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param user unique identifier for a client connected via websocket to the server.
   * @return unique identifier for a destination/topic
   */
  private String getDestinationIdBySubscription(
      final String simpSubscriptionId, final Principal user) {
    return destinationPerSubscription.get(simpSubscriptionId + "@" + user.getName());
  }

  /**
   * Associate a client, who subscribed to a destination, with it and optionally store additional
   * data for the destination, if this is the first time, someone subscribes to that destination.
   *
   * <p>If not, nothing is done with {@code defaultDestinationData}.
   *
   * @param user unique identifier for a client connected via websocket to the server.
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param destinationId unique identifier for the destination/topic, the user subscribed to
   * @param defaultDestinationData additional data, that is associated with the destination. It will
   *     only be stored, if there is no data stored for this destination/topic yet. If you do not
   *     wish to store addtional data, set it to {@code null}.
   */
  protected void handleSubscriptionHelper(
      final Principal user,
      @Header final String simpSubscriptionId,
      final String destinationId,
      final T defaultDestinationData) {
    System.out.println("User " + user.getName() + " subscribed for destination " + destinationId);

    final List<Principal> users =
        usersPerDestination.getOrDefault(destinationId, new ArrayList<>(1));

    // if the client is not already associated with an destination, add them
    // to the list of subscribed users for the destination.
    if (!users.contains(user)) {
      System.out.println("SyncController: Someone registered for " + destinationId);
      users.add(user);

      usersPerDestination.put(destinationId, users);
    }

    saveSubscription(simpSubscriptionId, user, destinationId);

    contents.putIfAbsent(destinationId, defaultDestinationData);
  }

  /**
   * If a client unsubscribes from a destination, the controller is sent a {@link
   * org.springframework.web.socket.messaging.SessionUnsubscribeEvent} containing information about
   * the affected user and subscription.
   *
   * <p>The controller can simply call this function with the event and it will be handled.
   *
   * <p>The association of the user to the destination will be deleted. If there will be no more
   * users associated with that destination at all, its additional data will also be erased.
   *
   * @param event event generated by Spring, informing the Application about a cancelled
   *     subscription.
   */
  protected void handleUnsubscribeHelper(final SessionUnsubscribeEvent event) {
    final Principal user = event.getUser();
    final String simpSubscriptionId =
        event.getMessage().getHeaders().get("simpSubscriptionId", String.class);

    final String destinationId = getDestinationIdBySubscription(simpSubscriptionId, user);
    if (destinationId != null) {
      System.out.println(
          "Got unsubscribe from "
              + event.getUser().getName()
              + " for destination id "
              + destinationId);

      final List<Principal> users =
          usersPerDestination.getOrDefault(destinationId, new ArrayList<>(0));

      users.remove(user);
      System.out.println(
          "Removed user " + user.getName() + " from destination id " + destinationId);

      if (users.isEmpty()) {
        System.out.println("Removed destination " + destinationId + ", since all users left.");
        usersPerDestination.remove(destinationId);
        contents.remove(destinationId);
      }
    }

    deleteSubscription(simpSubscriptionId, user);
  }

  /**
   * If a client disconnects his websocket from the server, the controller is sent a {@link
   * org.springframework.web.socket.messaging.SessionDisconnectEvent} containing information about
   * the affected user and subscription.
   *
   * <p>The controller can simply call this function with the event and it will be handled.
   *
   * <p>This method essentially acts in the same way as {@link #handleUnsubscribeHelper}, however,
   * instead of being removed from a single destination, the client will be removed from all
   * destinations they subscribed to.
   *
   * @param event event generated by Spring, informing the Application about a disconnected client.
   */
  protected void handleDisconnectHelper(final SessionDisconnectEvent event) {
    final Principal user = event.getUser();
    System.out.println("Disconnect of user " + user.getName());

    // remove from all destinations, if still present there
    final Set<String> keys = usersPerDestination.keySet();
    for (final String destinationId : keys) {
      final List<Principal> users =
          usersPerDestination.getOrDefault(destinationId, new ArrayList<>(0));

      if (users.contains(user)) {
        System.out.println("Removed user " + user.getName() + " from destination " + destinationId);
        users.remove(user);

        if (users.isEmpty()) {
          System.out.println("Removed destination " + destinationId + ", since all users left.");
          usersPerDestination.remove(destinationId);
          contents.remove(destinationId);
        }
      }
    }

    deleteSubscription(event.getSessionId(), user);
  }

  /**
   * Modify the additional content associated with a destination/topic
   *
   * @param destinationId id of the destination/topic, for which new additional shall be stored.
   * @param content New content to be stored for a destination/topic.
   */
  protected void setDestinationData(final String destinationId, final T content) {
    contents.put(destinationId, content);
  }

  /**
   * Query all clients associated with a destination/topic.
   *
   * @param destinationId id of the destination/topic, whose subscribed clients shall be listed by
   *     this method.
   */
  protected List<Principal> getUsersByDestinationId(final String destinationId) {
    return usersPerDestination.getOrDefault(destinationId, new ArrayList<>(0));
  }
}
