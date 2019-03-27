import { serverAddress } from './constants.ts';

/**
 * This function is called when content of the editor 
 * is supposed to be lint by the server. The function makes
 * a call to the lint endpoint.
 * 
 * @param {*} name - of the file to lint 
 * @param {*} sourceCode - of the file to lint 
 */
function lint(name, sourceCode) {
  var url = new URL(serverAddress + '/lint');

  const params = { name: name };

  url.search = new URLSearchParams(params);

  return fetch(url, {
    method: 'POST',
    mode: 'cors',
    headers: {
      Accept: 'application/json',
      'Content-Type': 'text/plain', //evtl java spezifisch stattdessen?
    },
    body: sourceCode,
  }).then(response => response.json());
}

export default lint;
