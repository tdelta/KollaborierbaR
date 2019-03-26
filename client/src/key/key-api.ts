import { serverAddress } from '../constants';

import OpenGoalInfo from './netdata/OpenGoalInfo';

import ProofResults from './netdata/ProofResults';
import ObligationResult from './netdata/ObligationResult';

export default class KeyApi {
  /**
   * Tells the server that it should prove all obligations in a file
   * @param string - the path to the file relative to the server projects folder
   * @returns a promise for the proof results
   */
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

  /**
   * Tells the server that it should prove some obligations
   * @param string - the path to the file relative to the server projects folder
   * @param nr - the index or indices of the obligations to prove
   * @returns a promise for the proof results
   */
  public proveObligations(
    path: string,
    nr: number | number[]
  ): Promise<ProofResults> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/proof/${escapedPath}?obligationIdxs=${nr}`;

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