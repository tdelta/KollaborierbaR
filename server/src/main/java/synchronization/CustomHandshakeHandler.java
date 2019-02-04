package synchronization;

import java.security.Principal;
import java.util.Map;
import java.util.UUID;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.server.ServerHttpRequest;
import org.springframework.stereotype.Service;
import org.springframework.web.socket.WebSocketHandler;
import org.springframework.web.socket.server.support.DefaultHandshakeHandler;

@Service
public class CustomHandshakeHandler extends DefaultHandshakeHandler {

  @Autowired private UserList userList;

  /**
   * Handles the websocket handshake when a user connects and returns an Object that identifies the
   * user. This enables us to target users with specific messages
   */
  @Override
  protected Principal determineUser(
      ServerHttpRequest request, WebSocketHandler wsHandler, Map<String, Object> attributes) {
    // Generate principal with UUID as name
    StompPrincipal stompPrincipal = new StompPrincipal(UUID.randomUUID().toString());
    System.out.println(userList);
    userList.addUser(stompPrincipal);
    return stompPrincipal;
  }
}
