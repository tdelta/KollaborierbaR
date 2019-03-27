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

/**
 * Provides access to websocket based communication with the backend server using
 * the <a href="https://stomp.github.io/">STOMP</a> protocol.
 *
 * Essentially, it allows to subscribe to a STOMP destination, and we will
 * receive all messages, the server posts to that destination.
 *
 * It is also possible to send messages messages without a subscription.
 *
 * This class is mainly utilized by
 * {@link ProofSyncController}
 * {@link ProjectSyncController}
 * {@link CollabController}
 * to synchronize data between the server and other clients, which are working
 * on the same project / file.
 */
export class StompService {
  private stompClient: Client;
  private subscriptions: Map<string, StompSubscription> = new Map();
  private callbacks: CallbackDef[] = [];

  constructor() {
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
      this.setCallbacks();
    };

    this.stompClient.onStompError = frame => {
      console.log(`Broker reported error: ${frame.headers.message}`);
      console.log(`Additional details: ${frame.body}`);
    };

    this.stompClient.activate();
  }

  /**
   * Users of this service may use this function to register callbacks for specific message types,
   * which will be invoked, whenever a message of that type arrives.
   *
   * Internally this works by creating stomp subscriptions.
   *
   * @deprecated use real subscriptions via {@link #safeSubscribe} instead.
   *
   * @param messageType - type of message, the callback should be invoked on
   * @param headers - any kind of message can be submitted with the internal subscription when stored in these headers
   * @param callback - will be invoked with a newly arrived message, if it belongs to the specified type
   */
  public on(
    messageType: string,
    headers: any,
    callback: (obj: IMessage) => void
  ) {
    this.callbacks.push({ messageType, headers, callback });
    this.setCallbacks();
  }

  /**
   * Used to remove callbacks placed by {@link #on}.
   * Dont confuse it with {@link #safeUnsubscribe}
   *
   * @deprecated please use {@link #safeSubscribe} and {@link #safeUnsubscribe} instead.
   *
   * @param messageType - message type, for which callbacks shall be no longer invoked.
   */
  public unsubscribe(messageType: string) {
    const prefixedMessageType = `/user/${messageType}`;

    this.callbacks = this.callbacks.filter(
      element => element.messageType !== prefixedMessageType
    );

    this.stompClient.unsubscribe(prefixedMessageType);
  }

  /**
   * Internal helper function, which enables the callbacks places by
   * {@link #on}
   *
   * @deprecated {@link #on} is deprecated.
   */
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

  /**
   * Subscribe to a STOMP destination (see
   * <a href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP 1.2 specification</a>
   * ) at the backend server.
   *
   * @param destination - destination which should be subscribed to
   * @param callback - invoked for each message arriving from that destination
   * @param headers - any kind of information can be submitted to the backend server alongside the
   *                  subscription using these headers
   * @returns a promise, indicating, whether the subscription completed, or not.
   */
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
          const sub = this.stompClient.subscribe(
            destination,
            callback,
            headers
          );

          this.subscriptions.set(destination, sub);
        }

        resolve();
      } else {
        reject('Could not subscribe, since we are not connected.');
      }
    });
  }

  /**
   * Unsubscribe from a STOMP destination (see
   * <a href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP 1.2 specification</a>
   * ) at the backend server.
   *
   * @param destination - destination from which should be unsubscribed
   * @returns a promise, indicating, whether the subscription has been cancelled, or not
   */
  public safeUnsubscribe(destination: string): Promise<void> {
    return new Promise((resolve, reject) => {
      if (this.subscriptions.has(destination) && this.stompClient.connected) {
        (this.subscriptions.get(
          destination
        ) as StompSubscription).unsubscribe();

        this.subscriptions.delete(destination);

        resolve();
      } else {
        reject(
          `Could not unsubscribe from ${destination}, because we are not subscribed, or not connected`
        );
      }
    });
  }

  /**
   * Sends a message to a STOMP destination
   *
   * @param destination - destination we subscribed to, and want to send a message to
   * @param headers - any kind of additional headers can be set
   * @param message - message sent at the destination
   */
  public sendMessageToDestination(
    messageType: string,
    headers: any,
    message: any
  ) {
    const serializedMessage = JSON.stringify(message);

    this.stompClient.publish({
      destination: messageType,
      headers: headers,
      body: serializedMessage,
    });
  }
}

/** internally used interface for storing callbacks, see {@link StompService#on} */
interface CallbackDef {
  messageType: string;
  headers: any;
  callback: (obj: IMessage) => void;
}
