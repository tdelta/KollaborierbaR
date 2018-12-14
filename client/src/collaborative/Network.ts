import io from 'socket.io-client';

export default class Network {
  private socket: SocketIOClient.Socket;

  constructor() {
    this.socket = io('http://localhost:3001');
  }

  public on(messageType: string, callback: (obj: any) => void) {
    this.socket.on(messageType, callback);
  }

  public broadcastOperation(operation: any) {
    const operationJSON = JSON.stringify(operation);

    this.socket.emit('operation', operationJSON);
  }
}
