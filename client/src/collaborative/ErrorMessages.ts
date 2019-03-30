import { ErrorEventObserver, ErrorEvent } from './ConsoleSyncController';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

/**
 * Observer that listens to events containing error messages and displays them.
 * Registers for events at {@link src/collaborative/ConsoleSyncController}
 */
export default class ErrorMessages implements ErrorEventObserver {
  private notificationSystem: RefObject<NotificationSystem.System>;

  /**
   * @param notificationSystem - Reference to a notification system that exists in the dom
   */
  constructor(notificationSystem: RefObject<NotificationSystem.System>) {
    this.notificationSystem = notificationSystem;
  }

  /**
   * Callback function for error message events. Forwards the content of the message to the notification system
   * @param msg - event containing the error message
   */
  public onErrorEvent(msg: ErrorEvent) {
    if (this.notificationSystem.current) {
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
