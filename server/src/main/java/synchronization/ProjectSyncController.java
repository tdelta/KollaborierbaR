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

@Controller
public class ProjectSyncController {
  // Project -> Editing users
  private ConcurrentHashMap<String, List<Principal>> sessions = new ConcurrentHashMap<>();

  // SubscriptionId@User -> Project
  private ConcurrentHashMap<String, String> subscriptions = new ConcurrentHashMap<>();

  private void saveSubscription(
      final String simpSubscriptionId, final Principal user, final String projectName) {
    subscriptions.put(simpSubscriptionId + "@" + user.getName(), projectName);
  }

  private void deleteSubscription(final String simpSubscriptionId, final Principal user) {
    subscriptions.remove(simpSubscriptionId + "@" + user.getName());
  }

  private String getProjectNameBySubscription(
      final String simpSubscriptionId, final Principal user) {
    return subscriptions.get(simpSubscriptionId + "@" + user.getName());
  }

  @Autowired private SimpMessagingTemplate messagingTemplate;
  @Autowired private UserList userList;

  @SubscribeMapping("/user/projects/{projectName}")
  public void handleProjectSubscription(
      final Principal user,
      @Header final String simpSubscriptionId,
      @DestinationVariable String projectName) {
    final String decodedProjectName = UriUtils.decode(projectName, "UTF-8");

    System.out.println(decodedProjectName);

    final List<Principal> users = sessions.getOrDefault(decodedProjectName, new ArrayList<>(1));

    if (!users.contains(user)) {
      System.out.println("Someone registered for " + decodedProjectName);
      users.add(user);

      sessions.put(decodedProjectName, users);
    }

    List<User> subscriberNames = getSubscriberNames(sessions.get(decodedProjectName));
    for (Principal otherUser : sessions.get(decodedProjectName)) {
      UsersUpdatedEvent userEvent =
          new UsersUpdatedEvent(this, decodedProjectName, subscriberNames);
      messagingTemplate.convertAndSendToUser(
          otherUser.getName(), "/projects/" + decodedProjectName, userEvent);
    }

    saveSubscription(simpSubscriptionId, user, decodedProjectName);
  }

  @EventListener
  public void handleUnsubscribe(final SessionUnsubscribeEvent event) {
    final Principal user = event.getUser();
    final String simpSubscriptionId =
        event.getMessage().getHeaders().get("simpSubscriptionId", String.class);

    final String projectName = getProjectNameBySubscription(simpSubscriptionId, user);

    System.out.println(
        "Got unsubscribe from " + event.getUser().getName() + " for project " + projectName);

    deleteSubscription(simpSubscriptionId, user);

    final List<Principal> users = sessions.getOrDefault(projectName, new ArrayList<>(0));

    List<User> subscriberNames = getSubscriberNames(users);
    UsersUpdatedEvent userEvent =
        new UsersUpdatedEvent(this, projectName, subscriberNames);
    for(Principal otherUser: users){
      messagingTemplate.convertAndSendToUser(
          otherUser.getName(), "/projects/" + projectName, userEvent);
    }

    System.out.println("Removed user " + user.getName() + " from project " + projectName);
    users.remove(user);
    if (users.isEmpty()) {
      System.out.println("Removed project " + projectName + ", since all users left.");
      sessions.remove(projectName);
    }
  }

  @EventListener
  public void handleDisconnect(final SessionDisconnectEvent event) {
    final Principal user = event.getUser();
    System.out.println("Disconnect of user " + user.getName());

    // remove from all projects, if still present there
    final Set<String> keys = sessions.keySet();
    for (final String project : keys) {
      final List<Principal> users = sessions.getOrDefault(project, new ArrayList<>(0));

      System.out.println("Removed user " + user.getName() + " from project " + project);
      users.remove(user);

      if (users.isEmpty()) {
        System.out.println("Removed project " + project + ", since all users left.");
        sessions.remove(project);
      }
    }

    deleteSubscription(event.getSessionId(), user);
  }

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

  @EventListener
  public void handleOpenedFile(final FileOpenedEvent event) {
    Principal user = event.getPrincipal();

    for (ConcurrentHashMap.Entry<String, List<Principal>> projectEntry : sessions.entrySet()) {
      if (projectEntry.getValue().contains(user)) {
        System.out.println(
            "Notifying users of project " + projectEntry.getKey() + " that a file was opened");
        HashMap<String, Object> headers = new HashMap<String, Object>();
        headers.put("file", event.getFile());
        for (Principal otherUser : projectEntry.getValue()) {
          List<User> subscriberNames = getSubscriberNames(projectEntry.getValue());
          UsersUpdatedEvent userEvent =
              new UsersUpdatedEvent(this, projectEntry.getKey(), subscriberNames);
          messagingTemplate.convertAndSendToUser(
              otherUser.getName(), "/projects/" + projectEntry.getKey(), userEvent, headers);
        }
      }
    }
  }

  private List<User> getSubscriberNames(List<Principal> subscriberList) {
    return userList
        .entrySet()
        .stream()
        .filter(x -> subscriberList.contains(x.getKey()))
        .map(x -> x.getValue())
        .collect(Collectors.toList());
  }

  private List<Principal> getUsersOfProject(final String projectName) {
    final List<Principal> users = sessions.getOrDefault(projectName, new ArrayList<>(0));

    return users;
  }
}
