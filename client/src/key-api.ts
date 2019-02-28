import { serverAddress } from './constants';

import OpenGoalInfo from './OpenGoalInfo';
import Node from './key/webui/prooftree/Node';

export default class KeyApi {
  public proveFile(path: string): Promise<ProofResults> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    const url = `${serverAddress}/proof/${escapedPath}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => response.json()); // parse the response body as json};
  }

  public proveObligation(path: string, nr: number): Promise<ProofResults> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/proof/${escapedPath}?obligationIdx=${nr}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => response.json()); // parse the response body as json};
  }
}

// define the structure received KeY results
export interface ProofResults {
  succeeded: ObligationResult[];
  failed: ObligationResult[];
  errors: ObligationResult[];
  openGoals: OpenGoalInfo[];
}

export interface ObligationResult {
  obligationIdx: number;
  resultMsg: string;
  proofTree: Node;
}
