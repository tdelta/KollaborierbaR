import { Network } from '../network';

import ProofNode from '../key/prooftree/ProofNode';
import ObligationResult from '../key/netdata/ObligationResult';

import { serverAddress } from '../constants';

export default class ProofCollabController {
  private network: Network;
  private observer: ProofEventObserver;
  private currentProjectName?: string;
  private currentFilePath?: string[];
  private currentTopic?: string;

  constructor(network: Network, observer: ProofEventObserver) {
    this.network = network;
    this.observer = observer;

    this.setObligationResult = this.setObligationResult.bind(this);
    this.genTopic = this.genTopic.bind(this);
    this.openFile = this.openFile.bind(this);
    this.closeFile = this.closeFile.bind(this);
  }

  private genTopic(projectName: string, path: string[]): string {
    return `/user/projects/proof/${projectName}/${path.join('/')}`;
  }

  public openFile(projectName: string, path: string[]): Promise<void> {
    const topic = this.genTopic(projectName, path);

    return this.network.safeSubscribe(
      topic,
      msg => {
        try {
          const event: ProofEvent = JSON.parse(msg.body);

          console.log(`incoming proof event`, event);
          
          switch(event.eventType) {
            case ProofEventType.UpdatedProof:
              this.observer.onUpdatedProof(event);
              break;

            case ProofEventType.UpdatedProofHistory:
              this.observer.onUpdatedHistory(event);
              break;
          }
        }
        
        catch (e) {
          console.error('Failed to parse server event');
          console.error(e);
        }
      },
      {}
    )
      .then(() => {
        this.currentProjectName = projectName;
        this.currentFilePath = path;
        this.currentTopic = topic;
      });
  }

  public closeFile(): Promise<void> {
    if (this.currentTopic == null) {
      return Promise.reject('There is no topic set, we can not close the current proof context');
    }

    else {
      return this.network.safeUnsubscribe(
        this.currentTopic
      );
    }
  }

  public setObligationResult(obligationResult: ObligationResult): void {
    if (this.currentTopic == null || this.currentFilePath == null || this.currentProjectName == null) {
      console.error('There is no topic set, we can not determine the current proof context');
    }

    else {
      const projectFilePath = `${this.currentProjectName}/${this.currentFilePath.join('/')}`;

      const url = `/proof/${this.currentProjectName}/${this.currentFilePath.join('/')}/obligation/${obligationResult.obligationIdx}/last`;

      console.log('Posting obligation result to ', url);

      fetch(`${serverAddress}/${url}`, {
        method: 'POST',
        mode: 'cors',
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(obligationResult), // necessary if you want to send a JSON object in a fetch request
      }).then(response => {
        if (response.status !== 200) {
          alert(
            'Uups! Something went wrong while posting your obligation result to the server'
          );
        }

        else {
          console.log("Uploaded obligation result to server", projectFilePath, url);
        }
      });
    }
  }

  public saveObligationResult(obligationResult: ObligationResult):void {
    if (this.currentTopic == null || this.currentFilePath == null || this.currentProjectName == null) {
      console.error('There is no topic set, we can not determine the current proof context');
    }

    else {
      const projectFilePath = `${this.currentProjectName}/${this.currentFilePath.join('/')}`;

      const url = `/proof/${this.currentProjectName}/${this.currentFilePath.join('/')}/obligation/${obligationResult.obligationIdx}/history`;

      console.log('Saving obligation result to ', url);

      fetch(`${serverAddress}/${url}`, {
        method: 'POST',
        mode: 'cors',
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(obligationResult), // necessary if you want to send a JSON object in a fetch request
      }).then(response => {
        if (response.status !== 200) {
          alert(
            'Uups! Something went wrong while saving your obligation proof result.'
          );
        }

        else {
          console.log("Saved obligation result to server", projectFilePath, url);
        }
      });
    }
  }
}

export enum ProofEventType {
  UpdatedProof = 'UpdatedProofEvent',
  UpdatedProofHistory = 'UpdatedProofHistoryEvent'
}

export interface ProofEvent {
  eventType: ProofEventType;
  projectName: string;
  filePath: string;
  obligationIdx: number;
}

export interface UpdatedProofEvent extends ProofEvent {}
export interface UpdatedProofHistoryEvent extends ProofEvent {}

interface ProofEventObserver {
  onUpdatedProof(
    event: ProofEvent
  ): void;

  onUpdatedHistory(
    event: ProofEvent
  ): void;
}
