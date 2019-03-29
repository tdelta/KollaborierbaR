package synchronization;

import events.DeletedFileEvent;
import events.DeletedProjectEvent;
import events.FileOpenedEvent;
import events.RenamedFileEvent;
import events.UpdatedFileEvent;
import events.UpdatedProjectEvent;
import events.UsersUpdatedEvent;
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

/**
 * Keeps track of clients, which want to be updated on changes to projects saved
 * on the server (see {@link server.ProofController}), and informs them about
 * such changes.
 *
 * <p>For this, this controller provides a STOMP topic/destination (see <a
 * href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP 1.2
 * specification</a>) for each project (constructed lazily).
 *
 * <p>Clients can then subscribe to it via a websocket and receive events (see {@link
 * events.ProjectEvent}), informing them about changes to the saved proofs regarding that file.
 *
 * <p>For this to work, {@link server.ProjectController} informs {@link
 * synchronization.ProjectSyncController} about changes via an {@link
 * org.springframework.context.ApplicationEventPublisher}.
 *
 * @todo since {@link server.ProofSyncController} there exists a new base class
 *       {@link server.SyncController} which helps handling subscriptions.
 *       Therefore, this class should be refactored to use it.
 *
 * @author Anton Haubner {@literal <anton.haubner@outlook.de>}
 */
@Controller
public class ProjectSyncController {
  /**
   * Associates a project name with users subscribed to it.
   *
   * Mapping: Project Name -> Editing Users
   */
  private ConcurrentHashMap<String, List<Principal>> sessions = new ConcurrentHashMap<>();

  /**
   * Associates an subscription id pared with a client with a project (name)
   *
   * Mapping: SubscriptionId@User -> Project name
   */
  private ConcurrentHashMap<String, String> subscriptions = new ConcurrentHashMap<>();

  /**
   * Helper method, stores a new association, of a client and their subscription id to a
   * project.
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param user unique identifier for a client connected via websocket to the server.
   * @param projectName name of the project, the client wants to subscribe to
   */
  private void saveSubscription(
      final String simpSubscriptionId, final Principal user, final String projectName) {
    subscriptions.put(simpSubscriptionId + "@" + user.getName(), projectName);
  }

  /**
   * Helper method, removes a client from receiving changes for a project by removing
   * its subscriptions.
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per user.
   * @param user unique identifier for a client connected via websocket to the server.
   */
  private void deleteSubscription(final String simpSubscriptionId, final Principal user) {
    subscriptions.remove(simpSubscriptionId + "@" + user.getName());
  }

  /**
   * Helper method, retrieves the name of a project a user is subscribed to, associated with the given
   * STOMP subscription id.
   *
   * @param simpSubscriptionId id STOMP generates for a subscription per client.
   * @param user unique identifier for a client connected via websocket to the server.
   * @return name of the project, the client subscribed to
   */
  private String getProjectNameBySubscription(
      final String simpSubscriptionId, final Principal user) {
    return subscriptions.get(simpSubscriptionId + "@" + user.getName());
  }

  /** Needed to send messages to clients via websocket */
  @Autowired private SimpMessagingTemplate messagingTemplate;

  /** Holds information about all users currently working on collaborative documents */
  @Autowired private UserList userList;

  /**
   * Provides a STOMP destination/topic for clients to subscribe to, see class description.
   *
   * @param headers STOMP headers. Filled in by Spring.
   * @param user unique identifier for a client connected via websocket to the server. Filled in by
   *     Spring.
   * @param simpSubscriptionId unique id, describing the new subscription
   * @param projectName name of the project for which the client wants to receive notifications about changes
   */
  @SubscribeMapping("/user/projects/{projectName}")
  public void handleProjectSubscription(
      final Principal user,
      @Header final String simpSubscriptionId,
      @DestinationVariable String projectName) {
    final String decodedProjectName = UriUtils.decode(projectName, "UTF-8");

    System.out.println("Decoded project name" + decodedProjectName);

    final List<Principal> users = sessions.getOrDefault(decodedProjectName, new ArrayList<>(1));

    // if the client is not already associated with a project, add them
    // to the list of subscribed users for the project.
    if (!users.contains(user)) {
      System.out.println("Someone registered for " + decodedProjectName);
      userList.setUniqueIdForProject(user, getSubscriberNames(users));
      users.add(user);
      sessions.put(decodedProjectName, users);
    }

    saveSubscription(simpSubscriptionId, user, decodedProjectName);

    // inform everyone in the project about the new user.
    broadcastUsernames(users, decodedProjectName);
  }

  /**
   * If a client unsubscribes from a project, the controller is sent a {@link
   * org.springframework.web.socket.messaging.SessionUnsubscribeEvent)} containing information about
   * the affected user and subscription.
   *
   * <p>The association of the user to the project will be deleted.
   *
   * @param event event generated by Spring, informing the Application about a cancelled
   *     subscription.
   */
  @EventListener
  public void handleUnsubscribe(final SessionUnsubscribeEvent event) {
    final Principal user = event.getUser();
    final String simpSubscriptionId =
        event.getMessage().getHeaders().get("simpSubscriptionId", String.class);

    final String projectName = getProjectNameBySubscription(simpSubscriptionId, user);
    if (projectName != null) {
      System.out.println(
          "Got unsubscribe from " + event.getUser().getName() + " for project " + projectName);

      final List<Principal> users = sessions.getOrDefault(projectName, new ArrayList<>(0));

      System.out.println("Removed user " + user.getName() + " from project " + projectName);
      users.remove(user);

      // inform every user of the project, that the list of users working at that
      // project changed (that someone left)
      broadcastUsernames(users, projectName);

      // remove all project session data, if there arent any users connected to the
      // project anymore
      if (users.isEmpty()) {
        System.out.println("Removed project " + projectName + ", since all users left.");
        sessions.remove(projectName);
      }
    }
    deleteSubscription(simpSubscriptionId, user);
  }

  /**
   * If a client disconnects his websocket from the server, the controller is sent a {@link
   * org.springframework.web.socket.messaging.SessionDisconnectEvent)} containing information about
   * the affected user and subscription.
   *
   * <p>This method essentially acts in the same way as {@link #handleUnsubscribe}, however,
   * instead of being removed from a single project, the client will be removed from all
   * projects they subscribed to.
   *
   * @param event event generated by Spring, informing the Application about a disconnected client.
   */
  @EventListener
  public void handleDisconnect(final SessionDisconnectEvent event) {
    final Principal user = event.getUser();
    System.out.println("Disconnect of user " + user.getName());

    // remove from all projects, if still present there
    final Set<String> keys = sessions.keySet();
    for (final String project : keys) {
      final List<Principal> users = sessions.getOrDefault(project, new ArrayList<>(0));
      if (users.contains(user)) {
        System.out.println("Removed user " + user.getName() + " from project " + project);
        users.remove(user);

        if (users.isEmpty()) {
          System.out.println("Removed project " + project + ", since all users left.");
          sessions.remove(project);
        }
        broadcastUsernames(users, project);
      }
    }
    deleteSubscription(event.getSessionId(), user);
  }

  /**
   * Called, whenever *something* changed about the structure of a project,
   * Currently this includes only the creation of new files.
   *
   * <p>It will inform all clients subscribed to the project about the
   * change by forwarding the received event.
   *
   * @param event indicates a change to the structure of a project.
   *              Contains information, which project changed.
   */
  @EventListener
  public void handleUpdatedProject(final UpdatedProjectEvent event) {
    System.out.println("Project updated: " + event.getProjectName());
    final List<Principal> users = getUsersOfProject(event.getProjectName());

    for (final Principal user : users) {
      System.out.println(
          "Sending project update to " + user.getName() + " at " + event.getProjectName());
      messagingTemplate.convertAndSendToUser(
          user.getName(), "/projects/" + event.getProjectName(), event);
    }
  }

  /**
   * Called, whenever a project got deleted.
   *
   * <p>It will inform all clients subscribed to the project about the
   * change by forwarding the received event.
   *
   * @param event indicates, which project got deleted.
   */
  @EventListener
  public void handleDeletedProject(final DeletedProjectEvent event) {
    System.out.println("Project deleted: " + event.getProjectName());
    final List<Principal> users = getUsersOfProject(event.getProjectName());
    sessions.remove(event.getProjectName());

    for (final Principal user : users) {
      System.out.println(
          "Sending project deletion to " + user.getName() + " at " + event.getProjectName());
      messagingTemplate.convertAndSendToUser(
          user.getName(), "/projects/" + event.getProjectName(), event);
    }
  }

  /**
   * Called, whenever a file in a project got deleted.
   *
   * <p>It will inform all clients subscribed to the project about the
   * change by forwarding the received event.
   *
   * @param event indicates, which file in which project got deleted.
   */
  @EventListener
  public void handleDeletedFile(final DeletedFileEvent event) {
    System.out.println("File deleted: " + event.getFilePath());
    final List<Principal> users = getUsersOfProject(event.getProjectName());

    for (final Principal user : users) {
      System.out.println(
          "Sending file deletion to " + user.getName() + " at " + event.getProjectName());
      messagingTemplate.convertAndSendToUser(
          user.getName(), "/projects/" + event.getProjectName(), event);
    }
  }

  /**
   * Called, whenever a file in a project got renamed.
   *
   * <p>It will inform all clients subscribed to the project about the
   * change by forwarding the received event.
   *
   * @param event indicates, which file in which project got renamed with which new name.
   */
  @EventListener
  public void handleRenamedFile(final RenamedFileEvent event) {
    System.out.println(
        "File renamed from " + event.getOriginalPath() + " to " + event.getNewPath());
    final List<Principal> users = getUsersOfProject(event.getProjectName());

    for (final Principal user : users) {
      System.out.println(
          "Sending file rename to " + user.getName() + " at " + event.getProjectName());
      messagingTemplate.convertAndSendToUser(
          user.getName(), "/projects/" + event.getProjectName(), event);
    }
  }

  /**
   * Called, whenever the content of a file in a project had been changed.
   *
   * <p>It will inform all clients subscribed to the project about the
   * change by forwarding the received event.
   *
   * @param event indicates, which file in which project changed its contents
   */
  @EventListener
  public void handleUpdatedFile(final UpdatedFileEvent event) {
    System.out.println("Contents updated of file  " + event.getFilePath());
    final List<Principal> users = getUsersOfProject(event.getProjectName());

    for (final Principal user : users) {
      System.out.println(
          "Sending file content update to " + user.getName() + " at " + event.getProjectName());
      messagingTemplate.convertAndSendToUser(
          user.getName(), "/projects/" + event.getProjectName(), event);
    }
  }

  /**
   * Called, whenever someone opened a file.
   *
   * (Event is usually issued by {@link synchronization.SynchronizationController})
   *
   * <p>It will inform all clients subscribed to the project about the new user
   * by forwarding the received event.
   *
   * @param event indicates, that some client started working on a file.
   */
  @EventListener
  public void handleOpenedFile(final FileOpenedEvent event) {
    final Principal user = event.getPrincipal();

    for (final ConcurrentHashMap.Entry<String, List<Principal>> projectEntry : sessions.entrySet()) {
      if (projectEntry.getValue().contains(user)) {
        System.out.println(
            "Notifying users of project " + projectEntry.getKey() + " that a file was opened");

        // collect all users working on the same file
        final HashMap<String, Object> headers = new HashMap<String, Object>();
        final headers.put("file", event.getFile());
        final List<User> subscriberNames = getSubscriberNames(projectEntry.getValue());

        final UsersUpdatedEvent userEvent =
            new UsersUpdatedEvent(this, projectEntry.getKey(), subscriberNames);

        // send an updated user list to everyone working on the file
        for (final Principal otherUser : projectEntry.getValue()) {
          final int idInProject = userList.getUniqueIdForProject(otherUser);

          userEvent.setOwnId(idInProject);
          messagingTemplate.convertAndSendToUser(
              otherUser.getName(), "/projects/" + projectEntry.getKey(), userEvent, headers);
        }
      }
    }
  }

  /**
   * Send information about a specific project to a list of users. The information consists of an
   * object per connected user containing: - Their id in a collaborative document - Their name
   *
   * @param users The users to send the information to
   * @param projectName The project that the information concerns
   */
  private void broadcastUsernames(List<Principal> users, String projectName) {
    List<User> subscriberNames = getSubscriberNames(users);
    UsersUpdatedEvent userEvent = new UsersUpdatedEvent(this, projectName, subscriberNames);
    for (Principal otherUser : users) {
      int idInProject = userList.getUniqueIdForProject(otherUser);
      userEvent.setOwnId(idInProject);
      messagingTemplate.convertAndSendToUser(
          otherUser.getName(), "/projects/" + projectName, userEvent);
    }
  }

  /**
   * From a list of websocket users, load their current user information saved in the UserList
   * Component. If there is no information saved about the user, they are excluded from the result.
   *
   * @param subscriberList Websocket user objects, obtained from websocket requests
   * @return A list of User objects containing information about the users - Their id in a
   *     collaborative document - Their name
   */
  private List<User> getSubscriberNames(List<Principal> subscriberList) {
    return userList.entrySet().stream()
        .filter(x -> subscriberList.contains(x.getKey()))
        .map(x -> x.getValue())
        .collect(Collectors.toList());
  }

  /**
   * @returns a list of clients, which are currently working on the specified project
   */
  private List<Principal> getUsersOfProject(final String projectName) {
    final List<Principal> users = sessions.getOrDefault(projectName, new ArrayList<>(0));

    return users;
  }
}
