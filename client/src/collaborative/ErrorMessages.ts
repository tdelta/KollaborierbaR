import {ErrorEventObserver, ErrorEvent} from './ConsoleSyncController';
import NotificationSystem from 'react-notification-system';
import {RefObject} from 'react';

export default class ErrorMessages implements ErrorEventObserver{

  private notificationSystem: RefObject<NotificationSystem.System>;

  constructor(notificationSystem: RefObject<NotificationSystem.System>){
    this.notificationSystem = notificationSystem;
  }

  public onErrorEvent(msg: ErrorEvent){
    if(this.notificationSystem.current){
      this.notificationSystem.current.addNotification({
        title: 'Error!',
        message: msg.message,
        level: 'error',
        position: 'bc',
        autoDismiss: 15,
      });
    }
  }
}
