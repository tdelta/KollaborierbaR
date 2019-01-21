package synchronization;

import synchronization.data.File;
import synchronization.data.LogootSAdd;
import synchronization.data.LogootSDel;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Collections;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.LinkedList;
import java.security.Principal;
import java.util.stream.Collectors;

import fr.loria.score.logootsplito.LogootSRopes;

import org.springframework.messaging.handler.annotation.MessageMapping;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.stereotype.Controller;
import org.springframework.messaging.simp.SimpMessagingTemplate;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.socket.server.support.DefaultHandshakeHandler;
import org.springframework.messaging.simp.annotation.SubscribeMapping;
import org.springframework.messaging.handler.annotation.Header;

@Controller
public class SynchronizationController {

// Map the currently connected Users to the document they are working on
private ConcurrentHashMap<String,LinkedList<Principal>> users = new ConcurrentHashMap<String,LinkedList<Principal>>();
private ConcurrentHashMap<String,LogootSRopes> documents = new ConcurrentHashMap<String,LogootSRopes>();

private Logger logger = LoggerFactory.getLogger(this.getClass());

// Autowired makes Spring magic fill this variable with a useful instance
@Autowired
private SimpMessagingTemplate messagingTemplate;

  @MessageMapping("/insert")
  public void greeting(@Header("file") String file, Principal user, LogootSAdd message) throws Exception {
    // Apply crdt operation on the document saved on the server
    message.execute(documents.get(file));
    // Send to everyone else who is connected
    for(Principal other: users.get(file)){
      if(!other.equals(user)){
        messagingTemplate.convertAndSendToUser(other.getName(), "/insert", message);
      }
    }
  }

  @MessageMapping("/remove")
  public void greeting(@Header("file") String file, Principal user, LogootSDel message) throws Exception {
    // Apply crdt operation on the document saved on the server
    message.execute(documents.get(file));
    // Send to everyone else who is connected
    for(Principal other: users.get(file)){
      if(!other.equals(user)){
        messagingTemplate.convertAndSendToUser(other.getName(), "/remove", message);
      }
    }
  }

  @MessageMapping("/file")
  public void handleSubscription(@Header("file") String file, Principal user,File text){
    unsubscribe(user);
    if(users.containsKey(file)){
      // There are already people working on this document
      LogootSRopes document = documents.get(file).copy();
      // Send the document to the user with a unique id (replicaNumber)
      document.setReplicaNumber(users.get(file).size());
      users.get(file).add(user);
      // Send document to user
      messagingTemplate.convertAndSendToUser(user.getName(),"/crdt-doc", document);
    }
    else {
      // Noone is working on this document yet
      LinkedList<Principal> subscribed = new LinkedList<Principal>();
      subscribed.add(user);
      users.put(file,subscribed);

      LogootSRopes document = new LogootSRopes();
      document.setReplicaNumber(0);
      // Insert content into the crdt document
      List<Character> characterList = text.content.chars().mapToObj(c -> (char) c).collect(Collectors.toList());
      // We have to construct the insert operation ourselfs because the java library doesnt generate the random part of the identifier,
      // leading to inconsistencies in mute-structs
      fr.loria.score.logootsplito.LogootSAdd<Character> insertOperation = new fr.loria.score.logootsplito.LogootSAdd<Character>(
          new fr.loria.score.logootsplito.Identifier(Arrays.asList(new Integer[]{1000,0,0}),0) ,characterList);
      insertOperation.execute(document);
      documents.put(file, document);
      // Send document to user
      messagingTemplate.convertAndSendToUser(user.getName(),"/crdt-doc", document);
    }
    logger.debug(users.get(file).toString());
  }

  private void unsubscribe(Principal user){
    // Iterate over all names of files and lists of users working on them
    for(ConcurrentHashMap.Entry<String,LinkedList<Principal>> entry: users.entrySet()){
      if(entry.getValue().contains(user)){
        if(entry.getValue().size()==1){
          // There are no other users working on the file, remove it entirely
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
