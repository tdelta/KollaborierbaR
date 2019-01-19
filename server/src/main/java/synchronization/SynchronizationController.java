package synchronization;

import java.util.Arrays;
import projectmanagement.*;
import server.ProjectController;

import synchronization.data.LogootSAdd;
import synchronization.data.LogootSDel;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.concurrent.ConcurrentHashMap;
import java.util.LinkedList;
import java.security.Principal;

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

@Autowired
private SimpMessagingTemplate messagingTemplate;

  @CrossOrigin
  @MessageMapping("/insert")
  public void greeting(@Header("file") String file, Principal user, LogootSAdd message) throws Exception {
    // Send to everyone else who is connected
    message.execute(documents.get(file));
    logger.info(documents.get(file).view());
    for(Principal other: users.get(file)){
      if(!other.equals(user)){
        messagingTemplate.convertAndSendToUser(other.getName(), "/insert", message);
      }
    }
  }

  @CrossOrigin
  @MessageMapping("/remove")
  public void greeting(@Header("file") String file, Principal user, LogootSDel message) throws Exception {
    // Send to everyone else who is connected
    message.execute(documents.get(file));
    logger.info(documents.get(file).view());
    for(Principal other: users.get(file)){
      if(!other.equals(user)){
        messagingTemplate.convertAndSendToUser(other.getName(), "/remove", message);
      }
    }
  }

  @SubscribeMapping("/user/crdt-doc")
  public void handleSubscription(@Header("file") String file, Principal user){
    if(users.containsKey(file)){
      // There are already people working on this document
      LogootSRopes document = documents.get(file).copy();
      // Send the document to the user with a unique id (replicaNumber)
      document.setReplicaNumber(users.get(file).size());
      users.get(file).add(user);
      messagingTemplate.convertAndSendToUser(user.getName(),"/crdt-doc", document);
    }
    else {
      // Noone is working on this document yet
      LinkedList<Principal> subscribed = new LinkedList<Principal>();
      subscribed.add(user);
      users.put(file,subscribed);
      documents.put(file,new LogootSRopes());
      messagingTemplate.convertAndSendToUser(user.getName(),"/crdt-doc", documents.get(file));
    }
  }
}
