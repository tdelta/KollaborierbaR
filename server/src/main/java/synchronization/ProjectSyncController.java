package synchronization;

import java.util.concurrent.ConcurrentHashMap;
import java.security.Principal;

import java.util.List;
import java.util.ArrayList;

import org.springframework.messaging.handler.annotation.MessageMapping;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.stereotype.Controller;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.socket.server.support.DefaultHandshakeHandler;
import org.springframework.messaging.simp.annotation.SubscribeMapping;
import org.springframework.messaging.handler.annotation.Header;
import org.springframework.messaging.handler.annotation.DestinationVariable;

import org.springframework.context.event.EventListener;

import events.TestEvent;
import events.UpdatedProjectEvent;
import events.DeletedProjectEvent;

@Controller
public class ProjectSyncController {
  // Project -> Editing users
  private ConcurrentHashMap<String, List<Principal>> sessions = new ConcurrentHashMap<>();

  @Autowired
  private SimpMessagingTemplate messagingTemplate;

  @MessageMapping("/projects/test")
  public void greeting(final Principal user) {
    System.out.println("User " + user.getName() + " tested!");
  }

  @SubscribeMapping("/user/projects/{projectName}")
  public void handleEventsSubscription(final Principal user, @DestinationVariable final String projectName){
    final List<Principal> users = sessions.getOrDefault(
        projectName,
        new ArrayList<>(1)
      );

    if (!users.contains(user)) {
      System.out.println("Someone registered for " + projectName);
      users.add(user);

      sessions.put(
          projectName, 
          users
      );
    }
  }

  @EventListener
  public void handleTestEvent(TestEvent event) {
    System.out.println(event.getMessage());
  }

  @EventListener
  public void handleUpdatedProject(final UpdatedProjectEvent event) {
    System.out.println("Project updated: " + event.getProjectPath());
    final List<Principal> users = getUsersOfProject(event.getProjectPath());

    for (final Principal user : users) {
      System.out.println("Sending project update to " + user.getName() + " at " + event.getProjectPath());
      messagingTemplate.convertAndSendToUser(user.getName(), "/projects/" + event.getProjectPath(), "ProjectUpdated");
    }
  }

  @EventListener
  public void handleDeletedProject(final DeletedProjectEvent event) {
    System.out.println("Project deleted: " + event.getProjectPath());
    final List<Principal> users = getUsersOfProject(event.getProjectPath());
    sessions.remove(event.getProjectPath());

    for (final Principal user : users) {
      System.out.println("Sending project deletion to " + user.getName() + " at " + event.getProjectPath());
      messagingTemplate.convertAndSendToUser(user.getName(), "/projects/" + event.getProjectPath(), "ProjectDeleted");
    }
  }

  private List<Principal> getUsersOfProject(final String projectName) {
    final List<Principal> users = sessions.getOrDefault(
        projectName,
        new ArrayList<>(0)
      );

    return users;
  }
}
