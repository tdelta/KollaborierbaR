import KeyApi, { ProofResults } from './key-api';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import OpenGoalInfo from './OpenGoalInfo';

export default class Key {
  private keyApi: KeyApi = new KeyApi();
  private getFilePath: () => string;
  private setProvenObligations: (provenObligations: number[]) => void;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private setOpenGoals: (openGoals: OpenGoalInfo[]) => void;

  private addNewConsoleMessage: (message: String) => void;

  constructor(
    notificationSystem: RefObject<NotificationSystem.System>,
    setProvenObligations: (provenObligations: number[]) => void,
    setOpenGoals: (openGoals: OpenGoalInfo[]) => void,
    getFilePath: () => string,
    addNewConsoleMessage: (message: String) => void
  ) {
    this.notificationSystem = notificationSystem;
    this.setProvenObligations = setProvenObligations;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligation = this.proveObligation.bind(this);
    this.setOpenGoals = setOpenGoals;

    this.sendNotifications = this.sendNotifications.bind(this);
    this.handleResults = this.handleResults.bind(this);

    this.addNewConsoleMessage = addNewConsoleMessage;
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

    this.keyApi.proveFile(this.getFilePath()).then(this.handleResults);
  }

  private sendNotifications(results: ProofResults): void {
    // print succeeded proofs as success notifications
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      for (const success of results.succeeded) {
        this.notificationSystem.current.addNotification({
          title: 'Success!',
          message: success.resultMsg,
          level: 'success',
          position: 'bc',
          autoDismiss: 15,
        });
      }
      // print fails as warnings
      for (const fail of results.failed) {
        this.notificationSystem.current.addNotification({
          title: 'Failure!',
          message: fail.resultMsg,
          level: 'warning',
          position: 'bc',
          autoDismiss: 15,
        });
      }
      // print exception messages as errors
      for (const error of results.errors) {
        this.notificationSystem.current.addNotification({
          title: 'Error!',
          message: error.resultMsg,
          level: 'error',
          position: 'bc',
          autoDismiss: 15,
        });
      }

      for(const stackTrace of results.stackTraces){
        this.addNewConsoleMessage(stackTrace.resultMsg);
      }
    }
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

    return this.keyApi
      .proveObligation(this.getFilePath(), nr)
      .then(this.handleResults);
  }

  private handleResults(results: ProofResults): void {
    const provenObligations: number[] = results.succeeded.map(
      success => success.obligationIdx
    );

    this.setProvenObligations(provenObligations);

    this.setOpenGoals(results.openGoals);

    this.sendNotifications(results);
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
        result[i] = numObligations - 1;
      }
    }
    return result;
  }
}
