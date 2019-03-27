package synchronization;

import events.UpdatedProofEvent;
import events.UpdatedProofHistoryEvent;
import java.security.Principal;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.event.EventListener;
import org.springframework.messaging.MessageHeaders;
import org.springframework.messaging.handler.annotation.DestinationVariable;
import org.springframework.messaging.handler.annotation.Header;
import org.springframework.messaging.handler.annotation.Headers;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.messaging.simp.annotation.SubscribeMapping;
import org.springframework.stereotype.Controller;
import org.springframework.web.socket.messaging.SessionDisconnectEvent;
import org.springframework.web.socket.messaging.SessionUnsubscribeEvent;
import org.springframework.web.util.UriUtils;

@Controller
public class ConsoleSyncController extends SyncController<Void> {
  private static String genProjectFilePath(final String projectName, final String filePath) {
    return projectName + '/' + filePath;
  }

  private static String genUserTopic(final String projectFilePath) {
    return "/console/" + projectFilePath;
  }

  /** Needed to send messages to clients via websocket */
  @Autowired private SimpMessagingTemplate messagingTemplate;

  @SubscribeMapping("/user/console/{projectName}/**")
  public void handleSubscription(
      @Headers final MessageHeaders headers,
      final Principal user,
      @Header final String simpSubscriptionId,
      @DestinationVariable String projectName) {
    final String projectFilePath;
    {
      final String decodedProjectName = UriUtils.decode(projectName, "UTF-8");

      // the file path needs to be extracted from the Header, since Spring
      // cant decode arbitrary paths (`/**`) for us.
      final String filePath =
          ((String) headers.get("simpDestination"))
              .substring(
                  "/user/console/".length()
                      + decodedProjectName.length()
                      + 1 // +1 for trailing /
                  );

      final String decodedFilePath = UriUtils.decode(filePath, "UTF-8");

      projectFilePath = genProjectFilePath(decodedProjectName, decodedFilePath);
    }

    System.out.println("ConsoleSyncController: User joined " + projectFilePath);

    // The base class {@link synchronization.SyncController} will help us to
    // keep track of the users.
    handleSubscriptionHelper(user, simpSubscriptionId, projectFilePath, null);
  }

  /**
   * Called, whenever a client unsubscribes from a STOMP destination.
   *
   * <p>This controller will then stop informing them about changes.
   */
  @EventListener
  public void handleUnsubscribe(final SessionUnsubscribeEvent event) {
    handleUnsubscribeHelper(event);
  }

  /**
   * Called, whenever a client's websocket disconnects.
   *
   * <p>This controller will then stop informing them about changes.
   */
  @EventListener
  public void handleDisconnect(final SessionDisconnectEvent event) {
    handleDisconnectHelper(event);
  }

  @EventListener
  public void handleNewMessage(final ConsoleMessageEvent event) {
    final String projectFilePath = genProjectFilePath(event.getProjectName(), event.getFilePath());
    final String topic = genUserTopic(projectFilePath);

    getUsersByDestinationId(projectFilePath)
        .forEach(
            iterationUser -> {
              messagingTemplate.convertAndSendToUser(iterationUser.getName(), topic, event);
            });
  }
}
