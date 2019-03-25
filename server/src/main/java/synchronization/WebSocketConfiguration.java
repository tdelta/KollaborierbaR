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

  /**
   * Used to configure converters for message payload and the
   * SimpMessagingTemplate that can address specific users
   *
   * @param config List of settings, initially empty
   */
  @Override
  public void configureMessageBroker(MessageBrokerRegistry config) {
    config.setUserDestinationPrefix("/user");
  }

  /**
   * Registers URLs for the websocket
   */
  @Override
  public void registerStompEndpoints(StompEndpointRegistry registry) {
    registry
        .addEndpoint("/websocket")
        .setAllowedOrigins("*")
        .setHandshakeHandler(customHandshakeHandler)
        .withSockJS();
  }
}
