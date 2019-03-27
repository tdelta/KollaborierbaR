import { serverAddress } from '../constants';

import OpenGoalInfo from './netdata/OpenGoalInfo';

import ProofResults from './netdata/ProofResults';
import ObligationResult from './netdata/ObligationResult';

/**
 * Provides methods to call HTTP routes of the backend server for KeY related
 * services it provides.
 */
export default class KeYApi {
  /**
   * Tells the server that it should prove all obligations in a file
   * @param string - the path to the file relative to the server projects folder
   * @param macro - path to the proof script to use, empty string for no proof script
   * @returns a promise for the proof results
   */
  public static proveFile(path: string, macro: string): Promise<ProofResults> {
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
   *
   * @param string - the path to the file relative to the server projects folder
   * @param nr - the index or indices of the obligations to prove
   * @param macro - path to the proof script to use, empty string for no proof script
   * @returns a promise for the proof results
   */
  public static proveObligations(
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

  /**
   * Downloads the most recent proof, a client set for a specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the latest proof
   *                        shall be retrieved.
   */
  public static downloadLatestProof(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): Promise<ObligationResult> {
    return fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/last`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    ).then(response => response.json());
  }

  /**
   * Downloads a list of all ids of proof results, which have been saved to the
   * server's history for a specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the ids of available
   *                        history items shall be retrieved
   */
  public static downloadHistoryIds(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): Promise<number[]> {
    return fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    ).then(response => response.json());
  }

  public static downloadObligationIds(
    projectName: string,
    filePath: string
  ): Promise<number[]> {
    return fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    ).then(response => response.json());
  }

  /**
   * Downloads a proof result, which had been saved by a client to the server's
   * history for a specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the result shall be
   *                        retrieved
   * @param historyIdx - which result shall be retrieved from the history?
   *                     {@link #downloadHistoryIds) can be used to retrieve a
   *                     list of ids available on the server.
   */
  public static downloadHistoricProof(
    projectName: string,
    filePath: string,
    obligationIdx: number,
    historyIdx: number
  ): Promise<ObligationResult> {
    return fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history/${historyIdx}`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    ).then(response => response.json());
  }

  /**
   * Deletes a proof result from the server's history for a
   * specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which a result shall be
   *                        deleted
   * @param historyIdx - which result shall be deleted from the history?
   *                     {@link #downloadHistoryIds) can be used to retrieve a
   *                     list of ids available on the server.
   */
  public static deleteHistoricProof(
    projectName: string,
    filePath: string,
    obligationIdx: number,
    historyIdx: number
  ): Promise<void> {
    return fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history/${historyIdx}`,
      {
        method: 'DELETE',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
      }
    ).then(response => {
      if (response.status !== 200) {
        alert('Uups! Failed to delete element from history.');
      } else {
        console.log('Successfully deleted element from history.');
      }
    });
  }

  /**
   * Sets the most recent proof for a specific file / obligation on the server,
   * so that it can be shared with other clients working on the same file.
   */
  public static saveHistoricProof(
    projectName: string,
    filePath: string,
    obligationResult: ObligationResult
  ): void {
    fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${
        obligationResult.obligationIdx
      }/history`,
      {
        method: 'POST',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(obligationResult), // necessary if you want to send a JSON object in a fetch request
      }
    ).then(response => {
      if (response.status !== 200) {
        alert('Uups! Failed to save obligation.');
      } else {
        console.log('Saved obligation result to server');
      }
    });
  }

  /**
   * Downloads a list of all proof results, which have been saved to the
   * server's history for a specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the available
   *                        history items shall be retrieved
   */
  public static downloadAllHistoricProofs(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ) {
    return KeYApi.downloadHistoryIds(projectName, filePath, obligationIdx).then(
      (historyIdxs: number[]) => {
        console.log('Retrieved history idxs: ', historyIdxs);

        return Promise.all(
          historyIdxs.map(historyIdx =>
            KeYApi.downloadHistoricProof(
              projectName,
              filePath,
              obligationIdx,
              historyIdx
            )
          )
        );
      }
    );
  }
}
