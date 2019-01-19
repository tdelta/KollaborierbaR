import Stomp from 'stompjs-websocket';
import SockJS from 'sockjs-client';

import {serverAddress} from '../constants'; 

export default class Network {
  private stompClient: Stomp.Client;
  private callbacks: CallbackDef[];
  private connected: boolean;

  constructor() {
    let socket = new SockJS(serverAddress+'/websocket');
    this.stompClient = Stomp.over(socket);
    this.callbacks = [];
    this.connected = false;
    
    //  this.stompClient.connect({},(frame) => {
    //    this.connected = true;
    //    this.setCallbacks();
    //  });
  }
  /*
  public on(messageType: string, headers: any, callback: (obj: any) => void) {
    this.callbacks.push({messageType, headers, callback});
    this.setCallbacks();
  }*/

  public on(callbacks: CallbackDef[]){
    this.stompClient.connect({},(frame) => {
    for(const callbackDef of callbacks){
    console.log(callbackDef);
        const {messageType, headers, callback} = callbackDef;
        this.stompClient.subscribe(
          `/user/${messageType}`,
          (message) => {callback(message.body)},
          headers
        );
      }
    });
  }
  
        

  public unsubscribe(messageType: string){
    this.callbacks = this.callbacks.filter((element) => element.messageType != messageType);
    this.stompClient.unsubscribe(messageType);
  }
  
  private setCallbacks(){
    if(this.connected){
      console.log(this.callbacks);
      for(const callbackDef of this.callbacks) {
        var {messageType,headers, callback} = callbackDef;
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

  public broadcast(messageType: string,headers: any, message: any) {
    const operationJSON = JSON.stringify(message);

    this.stompClient.send(`/${messageType}`,headers, operationJSON);
  }
}

interface CallbackDef {
  messageType: string,
  headers: any,
  callback: (obj: any) => void
}
