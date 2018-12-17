import {serverAddress, serverRoutes} from './constants.ts';

/**
 * Fetches contents and metadata of a file asynchronously from the server via
 * HTTP request.
 * 
 * @param {string} path: path to file that shall be opened.
 *     It shall contain a leading '/' and the first folder shall be the
 *     project name.
 *
 * @returns {Promise} promise which will resolve to said contents and metadata.
 *
 * @example
 * openFile('/My Project/README.md').then((response) =>
 *   console.log(response.fileName); // yields "README.md"
 *   console.log(response.fileText); // yields contents of the README.md file
 * });
 */
function openFile(path) {
    // API URL of the server we will use for our request
    const url = new URL(serverAddress + "/projects/" +path);

    return fetch(url, {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
            'Accept' : 'application/json', // we want a json object back
            //'Content-Type': 'application/json', // we are sending a json object
        },
    })
        .then((response) =>  response.json()); // parse the response body as json
}

export default openFile;
