import { Client, IMessage, IPublishParams, IFrame, StompHeaders, StompSubscription } from '@stomp/stompjs';
import SockJS from 'sockjs-client';

import {serverAddress} from './constants'; 

export enum ProjectEventType {
  UpdatedProject = 'UpdatedProjectEvent',
  DeletedProject = 'DeletedProjectEvent',
  DeletedFile = 'DeletedFileEvent'
}

export interface ProjectEvent {
    eventType: ProjectEventType;
    projectName: string;
}

export interface ProjectFileEvent extends ProjectEvent {
    filePath: string
}

interface EventObserver {
  onProjectEvent(event: ProjectEvent): void;
  onConnect(): void;
}

export class Network {
  private stompClient: Client;
  private observer: EventObserver;
  private subscriptions: Map<string, StompSubscription> = new Map();

  constructor(observer: EventObserver) {
    this.observer = observer;

    this.stompClient = new Client({
      webSocketFactory: () =>
      new SockJS(`${serverAddress}/websocket`),
      debug: console.log
    });

    this.stompClient.onUnhandledMessage = (msg: IMessage) => {
      console.log("WARNING: Did not handle message: " + msg.body);
    };

    this.stompClient.onUnhandledFrame = (frame: IFrame) => {
      console.log("WARNING: Did not handle frame: " + frame.body);
    };
    
    this.stompClient.onConnect = (frame) => {
      this.observer.onConnect();
    };
    
    this.stompClient.onStompError = function (frame) {
      console.log('Broker reported error: ' + frame.headers['message']);
      console.log('Additional details: ' + frame.body);
    };
    
    this.stompClient.activate();
  }

  private safePublish(params: IPublishParams, successCB?: () => void, errorCB?: () => void) {
    // TODO: Proper acks of server

    if (this.stompClient.connected) {
      this.stompClient.publish(params);

      if (successCB) {
        successCB();
      }
    }

    else if (errorCB) {
      errorCB();
    }
  }

  private safeSubscribe(
    destination: string,
    callback: (msg: IMessage) => void,
    headers: StompHeaders,
    successCB?: () => void,
    errorCB?: () => void
  ): void
  {
    // TODO: Proper acks of server

    if (this.stompClient.connected) {
      if (!this.subscriptions.has(destination)) { // dont subscribe, if we are already subscribed to that location
        const sub = this.stompClient.subscribe(
          destination,
          callback,
          headers
        );

        this.subscriptions.set(destination, sub);
      }

      if (successCB) {
        successCB();
      }
    }

    else if (errorCB) {
      errorCB();
    }
  }

  public closeProject(
    projectName: string,
    successCB?: () => void,
    errorCB?: () => void
  ): void {
    const topic = `/user/projects/${projectName}`;

    if (
         this.subscriptions.has(topic)
      && this.stompClient.connected
    ) {
      (<StompSubscription>this.subscriptions.get(topic)).unsubscribe();

      this.subscriptions.delete(topic);

      if (successCB) {
          successCB();
      }
    }

    else if (errorCB) {
      errorCB();
    }
  }

  public openProject(
    projectName: string,
    successCB?: () => void,
    errorCB?: () => void
  ):void
  {
    this.safeSubscribe(
      `/user/projects/${projectName}`,
      (msg) => {
        try {
          const event: ProjectEvent | ProjectFileEvent = JSON.parse(msg.body);

          console.log(`incoming event`);
          console.log(event);

          this.observer.onProjectEvent(
            event
          )
        }

        catch (e) {
            console.log('Failed to parse server event');
            console.log(e);
        }
      },
      {},
      successCB,
      errorCB
    );
  }
}
