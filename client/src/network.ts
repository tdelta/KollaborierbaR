import {
  Client,
  IMessage,
  IPublishParams,
  IFrame,
  StompHeaders,
  StompSubscription,
} from '@stomp/stompjs';
import SockJS, {Message} from 'sockjs-client';

import { serverAddress } from './constants';

export enum ProjectEventType {
  UpdatedProject = 'UpdatedProjectEvent',
  DeletedProject = 'DeletedProjectEvent',
  DeletedFile = 'DeletedFileEvent',
  RenamedFile = 'RenamedFileEvent',
  UpdatedFile = 'UpdatedFileEvent',
  UsersUpdated = 'UsersUpdatedEvent',
}

export interface ProjectEvent {
  eventType: ProjectEventType;
  projectName: string;
}

export interface ProjectFileEvent extends ProjectEvent {
  filePath: string;
}

export interface RenamedFileEvent extends ProjectEvent {
  originalPath: string;
  newPath: string;
}

export interface UsersUpdatedEvent extends ProjectEvent {
  users: User[];
}

export interface User {
  firstName: string;
  lastName: string;
  crdtId: number;
}

interface EventObserver {
  onProjectEvent(
    event: ProjectEvent | ProjectFileEvent | RenamedFileEvent
  ): void;
  onConnect(): void;
}

export class Network {
  private stompClient: Client;
  private observer: EventObserver;
  private subscriptions: Map<string, StompSubscription> = new Map();
  private callbacks: CallbackDef[] = [];

  constructor(observer: EventObserver) {
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

  public on(messageType: string, headers: any, callback: (obj: Message) => void) {
    this.callbacks.push({ messageType, headers, callback });
    this.setCallbacks();
  }

  public unsubscribe(messageType: string) {
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

  private safeSubscribe(
    destination: string,
    callback: (msg: IMessage) => void,
    headers: StompHeaders,
    successCB?: () => void,
    errorCB?: () => void
  ): void {
    // TODO: Proper acks of server

    if (this.stompClient.connected) {
      if (!this.subscriptions.has(destination)) {
        // dont subscribe, if we are already subscribed to that location
        const sub = this.stompClient.subscribe(destination, callback, headers);

        this.subscriptions.set(destination, sub);
      }

      if (successCB) {
        successCB();
      }
    } else if (errorCB) {
      errorCB();
    }
  }

  public closeProject(
    projectName: string,
    successCB?: () => void,
    errorCB?: () => void
  ): void {
    const topic = `/user/projects/${projectName}`;

    if (this.subscriptions.has(topic) && this.stompClient.connected) {
      (this.subscriptions.get(topic) as StompSubscription).unsubscribe();

      this.subscriptions.delete(topic);

      if (successCB) {
        successCB();
      }
    } else if (errorCB) {
      errorCB();
    }
  }

  public openProject(
    projectName: string,
    successCB?: () => void,
    errorCB?: () => void
  ): void {
    this.safeSubscribe(
      `/user/projects/${projectName}`,
      msg => {
        try {
          const event:
            | ProjectEvent
            | ProjectFileEvent
            | RenamedFileEvent
            | UsersUpdatedEvent = JSON.parse(msg.body);

          console.log(`incoming event`);
          console.log(event);

          this.observer.onProjectEvent(event);
        } catch (e) {
          console.log('Failed to parse server event');
          console.log(e);
        }
      },
      {},
      successCB,
      errorCB
    );
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
  callback: (obj: Message) => void;
}
