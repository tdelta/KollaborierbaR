import { serverAddress } from '../constants';

import OpenGoalInfo from './netdata/OpenGoalInfo';

import ProofResults from './netdata/ProofResults';
import ObligationResult from './netdata/ObligationResult';

export default class KeyApi {
  /**
   * Tells the server that it should prove all obligations in a file
   * @param string - the path to the file relative to the server projects folder
   * @param macro - path to the proof script to use, empty string for no proof script
   * @returns a promise for the proof results
   */
  public proveFile(path: string, macro: string): Promise<ProofResults> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    let url = `${serverAddress}/proof/${escapedPath}`;
    if (macro !== '') {
      url = `${url}?macro=${macro}`;
    }

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
   * @param macro - path to the proof script to use, empty string for no proof script
   * @returns a promise for the proof results
   */
  public proveObligations(
    path: string,
    nr: number | number[],
    macro: string
  ): Promise<ProofResults> {
    const escapedPath = escape(path);
    let url = `${serverAddress}/proof/${escapedPath}?obligationIdxs=${nr}`;
    if (macro !== '') {
      url = `${url}&macro=${macro}`;
    }

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
