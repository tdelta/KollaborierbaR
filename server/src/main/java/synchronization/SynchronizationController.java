package synchronization;

import synchronization.data.Delta;
import synchronization.data.WelcomeMessage;

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

@Controller
public class SynchronizationController {

// Map the currently connected Users to the document they are working on
private ConcurrentHashMap<Principal,String> users = new ConcurrentHashMap<Principal,String>();

@Autowired
private SimpMessagingTemplate messagingTemplate;

  @CrossOrigin
  @MessageMapping("/operation")
  public void greeting(Principal user, Delta message) throws Exception {
    // Send to everyone else who is connected
    String file = users.get(user);
    for(ConcurrentHashMap.Entry<Principal,String> other: users.entrySet()){
      if(other.getValue().equals(file) && !other.getKey().getName().equals(user.getName())){
        messagingTemplate.convertAndSendToUser(other.getKey().getName(), "/operation", message);
      }
    }
  }

  @MessageMapping("/retrive")
  public void retriveCrdtData(WelcomeMessage message){
    messagingTemplate.convertAndSendToUser(message.getUser(), "/welcome", message.getContent());
  }

  @SubscribeMapping("/user/operation")
  public void handleSubscription(@Header("file") String file, Principal user){
    for(ConcurrentHashMap.Entry<Principal,String> other: users.entrySet()){
      if(other.getValue().equals(file)){
        messagingTemplate.convertAndSendToUser(other.getKey().getName(), "/retrieve", "Hello");
      }
    }
    users.put(user,file);
  }
}
