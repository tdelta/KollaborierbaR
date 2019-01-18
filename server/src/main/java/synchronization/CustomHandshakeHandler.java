package synchronization;

import synchronization.StompPrincipal;
import java.security.Principal;
import java.util.Map;
import java.util.UUID;
import org.springframework.http.server.ServerHttpRequest;
import org.springframework.web.socket.WebSocketHandler;
import org.springframework.web.socket.server.support.DefaultHandshakeHandler;

public class CustomHandshakeHandler extends DefaultHandshakeHandler{
  /**
    * Handles the websocket handshake when a user connects and returns an Object that identifies the user.
    * This enables us to target users with specific messages
    */
  @Override
  protected Principal determineUser(ServerHttpRequest request, WebSocketHandler wsHandler, Map<String, Object> attributes) {
    // Generate principal with UUID as name
    Principal stompPrincipal = new StompPrincipal(UUID.randomUUID().toString());
    return stompPrincipal;
  }
}
