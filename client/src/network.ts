import {
  Client,
  IMessage,
  IPublishParams,
  IFrame,
  StompHeaders,
  StompSubscription,
} from '@stomp/stompjs';
import SockJS from 'sockjs-client';

import { serverAddress } from './constants';

interface NetworkObserver {
  onConnect(): void;
}

export class Network {
  private stompClient: Client;
  private observer: NetworkObserver;
  private subscriptions: Map<string, StompSubscription> = new Map();
  private callbacks: CallbackDef[] = [];

  constructor(observer: NetworkObserver) {
    this.observer = observer;

    this.stompClient = new Client({
      webSocketFactory: () => new SockJS(`${serverAddress}/websocket`),
      debug: console.log,
    });

    this.stompClient.onUnhandledMessage = (msg: IMessage) => {
      console.log(`WARNING: Did not handle message: ${msg.body}`);
    };

    this.stompClient.onUnhandledFrame = (frame: IFrame) => {
      console.log(`WARNING: Did not handle frame: ${frame.body}`);
    };

    this.stompClient.onConnect = frame => {
      this.observer.onConnect();
      this.setCallbacks();
    };

    this.stompClient.onStompError = frame => {
      console.log(`Broker reported error: ${frame.headers.message}`);
      console.log(`Additional details: ${frame.body}`);
    };

    this.stompClient.activate();
  }

  public on(
    messageType: string,
    headers: any,
    callback: (obj: IMessage) => void
  ) {
    this.callbacks.push({ messageType, headers, callback });
    this.setCallbacks();
  }

  public unsubscribe(messageType: string) {
    messageType = `/user/${messageType}`;
    this.callbacks = this.callbacks.filter(
      element => element.messageType !== messageType
    );
    this.stompClient.unsubscribe(messageType);
  }

  private setCallbacks() {
    if (this.stompClient.connected) {
      console.log(this.callbacks);
      while (this.callbacks.length > 0) {
        const callbackDef = this.callbacks.pop();
        if (callbackDef) {
          const { messageType, headers, callback } = callbackDef;
          console.log(messageType);
          console.log(callback);
          this.stompClient.subscribe(
            // Subscribe to the topic messagetype
            `/user/${messageType}`,
            // Execute callback when a message is received
            callback,
            // Send a header containing the filename we are working on
            headers
          );
        }
      }
    }
  }

  private safePublish(
    params: IPublishParams,
    successCB?: () => void,
    errorCB?: () => void
  ) {
    // TODO: Proper acks of server

    if (this.stompClient.connected) {
      this.stompClient.publish(params);

      if (successCB) {
        successCB();
      }
    } else if (errorCB) {
      errorCB();
    }
  }

  public safeSubscribe(
    destination: string,
    callback: (msg: IMessage) => void,
    headers: StompHeaders
  ): Promise<void> {
    return new Promise((resolve, reject) => {
      // TODO: Proper acks of server

      if (this.stompClient.connected) {
        if (!this.subscriptions.has(destination)) {
          // dont subscribe, if we are already subscribed to that location
          const sub = this.stompClient.subscribe(destination, callback, headers);

          this.subscriptions.set(destination, sub);
        }

        resolve();
      }
      
      else {
        reject('Could not subscribe, since we are not connected.');
      }
    });
  }

  public safeUnsubscribe(
    topic: string
  ): Promise<void> {
    return new Promise((resolve, reject) => {
      if (this.subscriptions.has(topic) && this.stompClient.connected) {
        (this.subscriptions.get(topic) as StompSubscription).unsubscribe();

        this.subscriptions.delete(topic);

        resolve();
      }
      
      else {
        reject(`Could not unsubscribe from ${topic}, because we are not subscribed, or not connected`);
      }
    });
  }

  public broadcast(messageType: string, headers: any, message: any) {
    const serializedMessage = JSON.stringify(message);

    this.stompClient.publish({
      destination: messageType,
      headers: headers,
      body: serializedMessage,
    });
  }
}

interface CallbackDef {
  messageType: string;
  headers: any;
  callback: (obj: IMessage) => void;
}
