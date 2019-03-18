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
import org.springframework.messaging.handler.annotation.MessageMapping;
import org.springframework.messaging.MessageHeaders;
import org.springframework.messaging.handler.annotation.Headers;
import org.springframework.context.ApplicationEventPublisher;

import proofutil.ProofNode;
import events.UpdatedProofEvent;

@Controller
public class ProofSyncController extends SyncController<Void> {
  private static String genProjectFilePath(final String projectName, final String filePath) {
    return projectName + '/' + filePath;
  }

  private static String genUserTopic(final String projectFilePath) {
    return "/projects/proof/" + projectFilePath;
  }

  @Autowired private SimpMessagingTemplate messagingTemplate;
  @Autowired private UserList userList;
  @Autowired private ApplicationEventPublisher applicationEventPublisher;

  @SubscribeMapping("/user/projects/proof/{projectName}/**")
  public void handleSubscription(
      @Headers final MessageHeaders headers,
      final Principal user,
      @Header final String simpSubscriptionId,
      @DestinationVariable String projectName
  ) {
    final String projectFilePath;
    {
      final String decodedProjectName = UriUtils.decode(projectName, "UTF-8");

      final String filePath = ((String) headers
        .get("simpDestination"))
        .substring(
            "/user/projects/proof/".length() + decodedProjectName.length() + 1 // +1 for trailing /
        );

      final String decodedFilePath = UriUtils.decode(filePath, "UTF-8");

      projectFilePath = genProjectFilePath(decodedProjectName, decodedFilePath);
    }

    System.out.println("ProofSyncController: User joined " + projectFilePath);

    handleSubscriptionHelper(
        user,
        simpSubscriptionId,
        projectFilePath,
        null
    );
  }

  @EventListener
  public void handleUnsubscribe(final SessionUnsubscribeEvent event) {
    handleUnsubscribeHelper(event);
  }

  @EventListener
  public void handleDisconnect(final SessionDisconnectEvent event) {
    handleDisconnectHelper(event);
  }

  @EventListener
  public void handleUpdatedProof(final UpdatedProofEvent event) {
    System.out.println("ProofSyncController: Proof updated of file  " + event.getFilePath() + " in project " + event.getProjectName() + " for obligation " + event.getObligationIdx());

    final String projectFilePath = genProjectFilePath(
          event.getProjectName(),
          event.getFilePath()
        );
    final String topic = genUserTopic(projectFilePath);

    System.out.println("ProofSyncController: Sending updates for users of " + projectFilePath + " to topic " + topic);

    getUsersByContentId(projectFilePath)
      .forEach(iterationUser -> {
        System.out.println("Sending updated obligation result event to " + iterationUser.getName() + " on topic " + topic);

        messagingTemplate.convertAndSendToUser(
            iterationUser.getName(),
            topic,
            event
        );
      });
  }

  //@MessageMapping("/setObligationResult")
  //public void handleSetObligationResult(@Header("file") String projectFilePath, Principal user, ProofResource proofResource)
  //    throws Exception {
  //  System.out.println("ProjectSyncController: Setting obligation result for " + projectFilePath);

  //  // Send to everyone
  //  getUsersByContentId(projectFilePath)
  //    .forEach(iterationUser -> {
  //      System.out.println("Sending obligation result url " + proofResource.url + " to " + iterationUser.getName() + " on topic " + genUserTopic(projectFilePath));

  //      messagingTemplate.convertAndSendToUser(
  //          iterationUser.getName(),
  //          genUserTopic(projectFilePath),
  //          new UpdatedProofEvent(this, proofResource.url)
  //      );
  //    });
  //}

  //private static class ProofResource {
  //  public String url;

  //  public ProofResource() { }

  //  public void setUrl(final String url) {
  //    this.url = url;
  //  }

  //  public String getUrl() {
  //    return this.url;
  //  }
  //}
}
