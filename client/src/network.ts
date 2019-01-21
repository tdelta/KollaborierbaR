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
  private callbacks: CallbackDef[] = [];

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
      this.setCallbacks();
    };
    
    this.stompClient.onStompError = function (frame) {
      console.log('Broker reported error: ' + frame.headers['message']);
      console.log('Additional details: ' + frame.body);
    };
    
    this.stompClient.activate();
  }

  public on(messageType: string, headers: any, callback: (obj: any) => void) {
    this.callbacks.push({messageType, headers, callback});
    this.setCallbacks();
  }

  public unsubscribe(messageType: string){
    this.callbacks = this.callbacks.filter((element) => element.messageType != messageType);
    this.stompClient.unsubscribe(messageType);
  }

  private setCallbacks(){
    if(this.stompClient.connected){
      console.log(this.callbacks);
      while(this.callbacks.length > 0) {
        const callbackDef = this.callbacks.pop();
        if(callbackDef){
          const {messageType,headers, callback} = callbackDef;
          console.log(messageType);
          console.log(callback);
          this.stompClient.subscribe(
            // Subscribe to the topic messagetype
            `/user/${messageType}`,
            // Execute callback when a message is received
            (message) => {callback(message.body)},
            // Send a header containing the filename we are working on
            headers
          );
        }
      }
    }
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

  public broadcast(messageType: string,headers: any,message: any){
    message = JSON.stringify(message);
    this.stompClient.publish(
      {destination: messageType, headers: headers, body: message}
    );
  }

  public openProject(projectPath: string, successCB?: () => void, errorCB?: () => void): void {
    this.safePublish(
      {destination: '/projects/openProject', body: 'lol'},
      successCB,
      errorCB
    );
  }
}

interface CallbackDef {
  messageType: string,
  headers: any,
  callback: (obj: any) => void
}
