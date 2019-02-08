package synchronization;

import events.FileOpenedEvent;
import fr.loria.score.logootsplito.LogootSRopes;
import java.security.Principal;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.ApplicationEventPublisher;
import org.springframework.messaging.handler.annotation.Header;
import org.springframework.messaging.handler.annotation.MessageMapping;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.stereotype.Controller;
import synchronization.data.File;
import synchronization.data.LogootSAdd;
import synchronization.data.LogootSDel;
import org.springframework.context.event.EventListener;
import org.springframework.web.socket.messaging.SessionDisconnectEvent;

@Controller
public class SynchronizationController {

  // Map the currently connected Users to the document they are working on
  private ConcurrentHashMap<String, LinkedList<Principal>> users =
      new ConcurrentHashMap<String, LinkedList<Principal>>();
  private ConcurrentHashMap<String, LogootSRopes> documents =
      new ConcurrentHashMap<String, LogootSRopes>();

  private Logger logger = LoggerFactory.getLogger(this.getClass());

  // Autowired makes Spring magic fill these variables with useful singleton instances
  @Autowired private SimpMessagingTemplate messagingTemplate;
  @Autowired private UserList userList;
  @Autowired private ApplicationEventPublisher applicationEventPublisher;

  @MessageMapping("/insert")
  public void greeting(@Header("file") String file, Principal user, LogootSAdd message)
      throws Exception {
    // Apply crdt operation on the document saved on the server
    message.execute(documents.get(file));
    // Send to everyone else who is connected
    for (Principal other : users.get(file)) {
      if (!other.equals(user)) {
        messagingTemplate.convertAndSendToUser(other.getName(), "/insert", message);
      }
    }
  }

  @MessageMapping("/remove")
  public void greeting(@Header("file") String file, Principal user, LogootSDel message)
      throws Exception {
    // Apply crdt operation on the document saved on the server
    message.execute(documents.get(file));
    // Send to everyone else who is connected
    for (Principal other : users.get(file)) {
      if (!other.equals(user)) {
        messagingTemplate.convertAndSendToUser(other.getName(), "/remove", message);
      }
    }
  }

  @MessageMapping("/reset")
  public void reset(@Header("file") String file, Principal user, File text) {
    LogootSRopes document = fromText(text.content);
    documents.put(file, document);
    document = document.copy();
    LinkedList<Principal> subscribed = users.get(file);
    for (int i = 0; i < subscribed.size(); i++) {
      document.setReplicaNumber(i);
      messagingTemplate.convertAndSendToUser(subscribed.get(i).getName(), "/crdt-doc", document);
    }
  }

  @EventListener
  public void handleDisconnect(final SessionDisconnectEvent event) {
    final Principal user = event.getUser();
    unsubscribe(user);
  }

  @MessageMapping("/file")
  public void handleSubscription(@Header("file") String file, Principal user, File text) {
    System.out.println("Adding user to crdt doc "+file);
    unsubscribe(user);
    int replicaNumber;
    if (users.containsKey(file)) {
      // There are already people working on this document
      LogootSRopes document = documents.get(file).copy();
      // Send the document to the user with a unique id (replicaNumber)
      replicaNumber = users.get(file).size();
      document.setReplicaNumber(replicaNumber);
      users.get(file).add(user);
      // Send document to user
      messagingTemplate.convertAndSendToUser(user.getName(), "/crdt-doc", document);
    } else {
      System.out.println("New crdt document, creating");
      // Noone is working on this document yet
      LinkedList<Principal> subscribed = new LinkedList<Principal>();
      subscribed.add(user);
      users.put(file, subscribed);

      LogootSRopes document = fromText(text.content);
      replicaNumber = 0;
      document.setReplicaNumber(replicaNumber);
      documents.put(file, document);
      // Send document to user
      messagingTemplate.convertAndSendToUser(user.getName(), "/crdt-doc", document);
    }
    // This event is handled by the ProjectSyncController instance
    userList.setId(user, replicaNumber);
    FileOpenedEvent event = new FileOpenedEvent(this, user, file);
    applicationEventPublisher.publishEvent(event);
  }

  private LogootSRopes fromText(String text) {
    LogootSRopes document = new LogootSRopes();

    if(text.length() > 0) {
      // Insert content into the crdt document
      List<Character> characterList =
          text.chars().mapToObj(c -> (char) c).collect(Collectors.toList());
      // We have to construct the insert operation ourselfs because the java library doesnt generate
      // the random part of the identifier,
      // leading to inconsistencies in mute-structs
      fr.loria.score.logootsplito.LogootSAdd<Character> insertOperation =
          new fr.loria.score.logootsplito.LogootSAdd<Character>(
              new fr.loria.score.logootsplito.Identifier(
                  Arrays.asList(new Integer[] {1000, 0, 0}), -1),
              characterList);
      insertOperation.execute(document);
    }
    return document;
  }

  private void unsubscribe(Principal user) {
    // Iterate over all names of files and lists of users working on them
    for (ConcurrentHashMap.Entry<String, LinkedList<Principal>> entry : users.entrySet()) {
      if (entry.getValue().contains(user)) {
        System.out.println("Removed user "+user.getName()+" from crdt doc "+entry.getKey());
        if (entry.getValue().size() == 1) {
          for(Principal otherUser: entry.getValue()){
            System.out.println(user.getName());
          }
          // There are no other users working on the file, remove it entirely
          System.out.println("Removed crdt doc "+entry.getKey());
          users.remove(entry.getKey());
          documents.remove(entry.getKey());
        } else {
          // Remove the user from the file
          entry.getValue().remove(user);
        }
      }
    }
  }
}
