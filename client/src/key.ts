import KeyApi, {ProofResults} from './key-api';
import NotificationSystem from 'react-notification-system';
import {RefObject} from 'react';

export default class Key{

  private keyApi: KeyApi = new KeyApi();
  private getFilePath: () => string;
  private notificationSystem: RefObject<NotificationSystem.System>;

  constructor(
    notificationSystem: RefObject<NotificationSystem.System>,
    getFilePath: () => string
  ){
    this.notificationSystem = notificationSystem;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligation = this.proveObligation.bind(this);
  } 

  private proveFile() {
    if (this.notificationSystem.current) {
        this.notificationSystem.current.clearNotifications();
        this.notificationSystem.current.addNotification({
            title: 'Please Wait!',
            message: 'Running proof obligations...',
            level: 'info',
            position: 'bc',
            autoDismiss: 0
        });
    }
    this.keyApi.proveFile(this.getFilePath())
        .then((response: ProofResults) => {  
            // print succeeded proofs as success notifications
            if (this.notificationSystem.current) {
            this.notificationSystem.current.clearNotifications();
                for (let i in response.succeeded) {
                    this.notificationSystem.current.addNotification({
                        title: 'Success!',
                        message: response.succeeded[i],
                        level: 'success',
                        position: 'bc',
                        autoDismiss: 15
                    });
            }
            // print fails as warnings
            for (let i in response.failed) {
                    this.notificationSystem.current.addNotification({
                        title: 'Failure!',
                        message: response.failed[i],
                        level: 'warning',
                        position: 'bc',
                        autoDismiss: 15
                    });
            }
            // print exception messages as errors
            for (let i in response.errors) {
                    this.notificationSystem.current.addNotification({
                        title: 'Error!',
                        message: response.errors[i],
                        level: 'error',
                        position: 'bc',
                        autoDismiss: 15
                    });
            }
        }
    });
  }

  public proveObligation(nr: number){ 
    if (this.notificationSystem.current) {
        this.notificationSystem.current.clearNotifications();
        this.notificationSystem.current.addNotification({
            title: 'Please Wait!',
            message: 'Running proof obligation...',
            level: 'info',
            position: 'bc',
            autoDismiss: 0
        });
    }
    this.keyApi.proveObligation(this.getFilePath(),nr).then((answer: any) => {
      alert('JAY');
    });
  }

  /**
   * Finds all lines that contain proof obligations and gives each obligation an index.
   * @param Lines of a text that contains JML specifications
   * @result An array where the index of a line that contains proof obligations
   *    is set to the index of the last obligations in the line. For the other lines it is undefined
   */
  public getObligations(lines: string[]): number[]{
    let numObligations = 0;
    let result: number[] = [];
    for(let i in lines){
      // Find the start of all proof obligations in the current line
      let regex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
      let obligations: RegExpMatchArray | null = lines[i].match(regex);
      if(obligations){
        numObligations += obligations.length;
        result[i] = numObligations;
      }
    }
    return result;
  }

}
