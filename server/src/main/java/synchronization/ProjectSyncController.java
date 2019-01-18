package synchronization;

import java.util.concurrent.ConcurrentHashMap;
import java.security.Principal;

import org.springframework.messaging.handler.annotation.MessageMapping;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.stereotype.Controller;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.socket.server.support.DefaultHandshakeHandler;
import org.springframework.messaging.simp.annotation.SubscribeMapping;
import org.springframework.messaging.handler.annotation.Header;

import org.springframework.context.event.EventListener;

import server.TestEvent;

@Controller
public class ProjectSyncController {
  // Map the Principal sec objects to project data
  private ConcurrentHashMap<Principal, Project> sessions = new ConcurrentHashMap<>();

  @Autowired
  private SimpMessagingTemplate messagingTemplate;

  @MessageMapping("/projects/test")
  public void greeting(final Principal user) {
    System.out.println("User " + user.getName() + " tested!");
  }

  @SubscribeMapping("/projects/openProject")
  public void handleEventsSubscription(final Principal user, final String projectPath){
    sessions.put(
        user, 
        new Project(projectPath)
    );
  }

  @EventListener
  public void handleContextRefresh(TestEvent event) {
    System.out.println(event.getMessage());
  }
}
