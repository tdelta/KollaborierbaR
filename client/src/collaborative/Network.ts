import Stomp from 'stompjs-websocket';
import SockJS from 'sockjs-client';

export default class Network {
  private stompClient: Stomp.Client;

  constructor() {
    let socket = new SockJS('http://localhost:9000/websocket');
    this.stompClient = Stomp.over(socket);
  }

  public on(messageType: string, callback: (obj: any) => void) {
    this.stompClient.connect({},(frame) => {
        this.stompClient.subscribe(
          // Subscribe to the topic messagetype
          `/user/${messageType}`,
          // Execute callback when a message is received
          (message) => {callback(message.body)},
          // Send a header containing the filename we are working on
          {'file': 'TODO.java',}
        );
    });
  }

  public broadcastOperation(operation: any) {
    const operationJSON = JSON.stringify(operation);

    this.stompClient.send('/operation',{}, operationJSON);
  }
}
