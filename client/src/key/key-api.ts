import { serverAddress } from '../constants';

import OpenGoalInfo from './netdata/OpenGoalInfo';

import ProofResults from './netdata/ProofResults';
import ObligationResult from './netdata/ObligationResult';

export default class KeyApi {
  public proveFile(path: string, macro: string | null): Promise<ProofResults> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    const url = `${serverAddress}/proof/${escapedPath}?macro=${macro}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => response.json()); // parse the response body as json};
  }

  public proveObligations(
    path: string,
    nr: number | number[],
    macro: string | null
  ): Promise<ProofResults> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/proof/${escapedPath}?obligationIdxs=${nr}&macro=${macro}`;

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
