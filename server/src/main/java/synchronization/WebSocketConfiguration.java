package synchronization;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Configuration;
import org.springframework.messaging.simp.config.MessageBrokerRegistry;
import org.springframework.stereotype.Controller;
import org.springframework.web.socket.config.annotation.EnableWebSocketMessageBroker;
import org.springframework.web.socket.config.annotation.StompEndpointRegistry;
import org.springframework.web.socket.config.annotation.WebSocketMessageBrokerConfigurer;

@Configuration
@EnableWebSocketMessageBroker
@Controller
public class WebSocketConfiguration implements WebSocketMessageBrokerConfigurer {

  @Autowired private CustomHandshakeHandler customHandshakeHandler;

  @Override
  public void configureMessageBroker(MessageBrokerRegistry config) {
    config.setUserDestinationPrefix("/user");
    // config.enableSimpleBroker("/projects");
  }

  @Override
  public void registerStompEndpoints(StompEndpointRegistry registry) {
    registry
        .addEndpoint("/websocket")
        .setAllowedOrigins("*")
        .setHandshakeHandler(customHandshakeHandler)
        .withSockJS();
  }
}
