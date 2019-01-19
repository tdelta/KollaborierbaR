import { Client, IMessage, IPublishParams } from '@stomp/stompjs';
import SockJS from 'sockjs-client';

import {serverAddress} from './constants'; 

enum ProjectEvent {
  nom
}

interface EventObserver {
  onProjectEvent(event: ProjectEvent, message: any): void;
}

export default class Network {
  private stompClient: Client;
  private observer: EventObserver;

  constructor(observer: EventObserver) {
    this.observer = observer;

    this.stompClient = new Client({
      webSocketFactory: () =>
      new SockJS(`${serverAddress}/websocket`),
      debug: console.log
    });
    
    this.stompClient.onConnect = (frame) => {
      this.stompClient.subscribe(
        "/projects/events",
        (msg) => {
          const eventStr: string = msg.headers.event;
          let event: ProjectEvent | undefined = undefined;

          switch (eventStr) {
            case 'nom':
              event = ProjectEvent.nom;
              break;
          }

          if (event) {
            this.observer.onProjectEvent(
              event, msg.body
            )
          }

          else {
            console.log(`Received unknown project event: ${eventStr}`);
          }
        }
      );
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

  public openProject(projectPath: string, successCB?: () => void, errorCB?: () => void): void {
    this.safePublish(
      {destination: '/projects/openProject', body: 'lol'},
      successCB,
      errorCB
    );
  }
}
