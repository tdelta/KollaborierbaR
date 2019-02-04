import KeyApi, { ProofResults } from './key-api';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import OpenGoalInfo from './OpenGoalInfo';

export default class Key {
  private keyApi: KeyApi = new KeyApi();
  private getFilePath: () => string;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private setOpenGoals: (openGoals: OpenGoalInfo[]) => void;

  constructor(
    notificationSystem: RefObject<NotificationSystem.System>,
    setOpenGoals: (openGoals: OpenGoalInfo[]) => void,
    getFilePath: () => string
  ) {
    this.notificationSystem = notificationSystem;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligation = this.proveObligation.bind(this);
    this.setOpenGoals = setOpenGoals;
  }

  private proveFile() {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      this.notificationSystem.current.addNotification({
        title: 'Please Wait!',
        message: 'Running proof obligations...',
        level: 'info',
        position: 'bc',
        autoDismiss: 0,
      });
    }
    this.keyApi.proveFile(this.getFilePath()).then((response: ProofResults) => {
      // print succeeded proofs as success notifications
      if (this.notificationSystem.current) {
        this.notificationSystem.current.clearNotifications();
        for (const success of response.succeeded) {
          this.notificationSystem.current.addNotification({
            title: 'Success!',
            message: success,
            level: 'success',
            position: 'bc',
            autoDismiss: 15,
          });
        }
        // print fails as warnings
        for (const fail of response.failed) {
          this.notificationSystem.current.addNotification({
            title: 'Failure!',
            message: fail,
            level: 'warning',
            position: 'bc',
            autoDismiss: 15,
          });
        }
        // print exception messages as errors
        for (const error of response.errors) {
          this.notificationSystem.current.addNotification({
            title: 'Error!',
            message: error,
            level: 'error',
            position: 'bc',
            autoDismiss: 15,
          });
        }

        this.setOpenGoals(response.openGoals);
      }
    });
  }

  public proveObligation(nr: number) {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      this.notificationSystem.current.addNotification({
        title: 'Please Wait!',
        message: 'Running proof obligation...',
        level: 'info',
        position: 'bc',
        autoDismiss: 0,
      });
    }
    this.keyApi.proveObligation(this.getFilePath(), nr).then((answer: any) => {
      alert('JAY');
    });
  }

  /**
   * Finds all lines that contain proof obligations and gives each obligation an index.
   * @param Lines of a text that contains JML specifications
   * @result An array where the index of a line that contains proof obligations
   *    is set to the index of the last obligations in the line. For the other lines it is undefined
   */
  public getObligations(lines: string[]): number[] {
    let numObligations = 0;
    const result: number[] = [];
    for (let i = 0; i < lines.length; i += 1) {
      // Find the start of all proof obligations in the current line
      const regex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
      const obligations: RegExpMatchArray | null = lines[i].match(regex);
      if (obligations) {
        numObligations += obligations.length;
        result[i] = numObligations;
      }
    }
    return result;
  }
}
