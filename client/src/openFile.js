function openFile(path) {
    const url = new URL('http://localhost:8080/projects/openFile');

    const body = { 
        'path':  path
    };

    console.log(body);

    return fetch(url, {
        method: 'POST',
        mode: 'cors',
        headers: {
            'Accept' : 'application/json',
            'Content-Type': 'application/json', //evtl java spezifisch stattdessen?
        },
        body: JSON.stringify(body)
    })
        .then((response) =>  response.json());
}

export default openFile;
