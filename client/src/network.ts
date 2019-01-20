import { Client, IMessage, IPublishParams, IFrame, StompHeaders } from '@stomp/stompjs';
import SockJS from 'sockjs-client';

import {serverAddress} from './constants'; 

export enum ProjectEvent {
  ProjectUpdated = 'ProjectUpdated',
  ProjectDeleted = 'ProjectDeleted'
}

interface EventObserver {
  onProjectEvent(event: ProjectEvent, message: any): void;
  onConnect(): void;
}

export class Network {
  private stompClient: Client;
  private observer: EventObserver;

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
      this.stompClient.subscribe(
        destination,
        callback,
        headers
      );

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
        const eventStr: string = msg.body;
        console.log(`incoming ${eventStr}`);

        if (eventStr in ProjectEvent) {
          this.observer.onProjectEvent(
            ProjectEvent[eventStr as keyof typeof ProjectEvent], msg.body
          )
        }

        else {
          console.log(`Received unknown project event: ${eventStr}`);
        }
      },
      {},
      successCB,
      errorCB
    );
  }
}
