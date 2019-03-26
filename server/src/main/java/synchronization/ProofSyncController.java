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

/**
 * Keeps track of clients, which want to be updated on changes to the server proof history (see
 * {@link server.ProofController}), and informs them about such changes.
 *
 * <p>For this, this controller provides a STOMP topic/destination (see <a
 * href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP 1.2
 * specification</a>) for each file in each project (constructed lazily).
 *
 * <p>Clients can then subscribe to it via a websocket and receive events (see {@link
 * events.ProofEvent}), informing them about changes to the saved proofs regarding that file.
 *
 * <p>For this to work, {@link server.ProofController} informs {@link
 * synchronization.ProofSyncController} about changes via an {@link
 * org.springframework.context.ApplicationEventPublisher}.
 *
 * @author Anton Haubner {@literal <anton.haubner@outlook.de>}
 */
@Controller
public class ProofSyncController extends SyncController<Void> {
  /**
   * Helper function, which concatenates a project name and a file path to one path string.
   *
   * @param projectName name of a project stored on the server
   * @param filePath path to a file within the project
   * @return concatenation as described with a `/` in between.
   */
  private static String genProjectFilePath(final String projectName, final String filePath) {
    return projectName + '/' + filePath;
  }

  /**
   * Each STOMP destination/topic is identified by an unique string. This function can generate this
   * identifier, using a path to the corresponding file.
   *
   * @param projectFilePath path to a file, for which the destination identifier is wanted, starting
   *     with the project name as root node. (see also {@link #genProjectFilePath}).
   * @return STOMP destination identifier as described.
   */
  private static String genUserTopic(final String projectFilePath) {
    return "/projects/proof/" + projectFilePath;
  }

  /** Needed to send messages to clients via websocket */
  @Autowired private SimpMessagingTemplate messagingTemplate;

  /**
   * Provides a STOMP destination/topic for clients to subscribe to, see class description.
   *
   * @param headers STOMP headers. Filled in by Spring.
   * @param user unique identifier for a client connected via websocket to the server. Filled in by
   *     Spring.
   * @param simpSubscriptionId unique id, describing the new subscription
   * @param projectName name of the project, where the file resides, whose proofs is being
   *     subscribed to.
   */
  @SubscribeMapping("/user/projects/proof/{projectName}/**")
  public void handleSubscription(
      @Headers final MessageHeaders headers,
      final Principal user,
      @Header final String simpSubscriptionId,
      @DestinationVariable String projectName) {
    /**
     * destination names are being generated from project file paths (@see #genProjectFilePath).
     * Using this name, this controller keeps track of which users are subscribed to what file.
     * Therefore, we need to find out this path name.
     */
    final String projectFilePath;
    {
      final String decodedProjectName = UriUtils.decode(projectName, "UTF-8");

      // the file path needs to be extracted from the Header, since Spring
      // cant decode arbitrary paths (`/**`) for us.
      final String filePath =
          ((String) headers.get("simpDestination"))
              .substring(
                  "/user/projects/proof/".length()
                      + decodedProjectName.length()
                      + 1 // +1 for trailing /
                  );

      final String decodedFilePath = UriUtils.decode(filePath, "UTF-8");

      projectFilePath = genProjectFilePath(decodedProjectName, decodedFilePath);
    }

    System.out.println("ProofSyncController: User joined " + projectFilePath);

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

  /**
   * Called, whenever the proof result, temporarily stored for each proof obligation by {@link
   * server.ProofController} (see also {@link server.ProofController#getCurrentProof} or {@link
   * server.ProofController#uploadCurrentObligationResult}), has been changed.
   *
   * <p>It will inform all clients subscribed to the corresponding STOMP destination about the
   * change.
   *
   * @param event information, which obligation is affected by the change
   */
  @EventListener
  public void handleUpdatedProof(final UpdatedProofEvent event) {
    System.out.println(
        "ProofSyncController: Proof updated of file  "
            + event.getFilePath()
            + " in project "
            + event.getProjectName()
            + " for obligation "
            + event.getObligationIdx());

    final String projectFilePath = genProjectFilePath(event.getProjectName(), event.getFilePath());
    final String topic = genUserTopic(projectFilePath);

    System.out.println(
        "ProofSyncController: Sending updates for users of "
            + projectFilePath
            + " to topic "
            + topic);

    getUsersByContentId(projectFilePath)
        .forEach(
            iterationUser -> {
              System.out.println(
                  "Sending updated obligation result event to "
                      + iterationUser.getName()
                      + " on topic "
                      + topic);

              messagingTemplate.convertAndSendToUser(iterationUser.getName(), topic, event);
            });
  }

  /**
   * Called, whenever the history of proof results, stored for each proof obligation by {@link
   * server.ProofController} (see also {@link server.ProofController#addToHistory} or {@link
   * server.ProofController#deleteFromHistory}), has been changed.
   *
   * <p>It will inform all clients subscribed to the corresponding STOMP destination about the
   * change.
   *
   * @param event information, which obligation is affected by the change
   */
  @EventListener
  public void handleUpdatedProofHistory(final UpdatedProofHistoryEvent event) {
    System.out.println(
        "ProofSyncController: Proof history updated of file  "
            + event.getFilePath()
            + " in project "
            + event.getProjectName()
            + " for obligation "
            + event.getObligationIdx());

    final String projectFilePath = genProjectFilePath(event.getProjectName(), event.getFilePath());
    final String topic = genUserTopic(projectFilePath);

    System.out.println(
        "ProofSyncController: Sending history updates for users of "
            + projectFilePath
            + " to topic "
            + topic);

    getUsersByContentId(projectFilePath)
        .forEach(
            iterationUser -> {
              System.out.println(
                  "Sending updated history event to "
                      + iterationUser.getName()
                      + " on topic "
                      + topic);

              messagingTemplate.convertAndSendToUser(iterationUser.getName(), topic, event);
            });
  }
}
