function lint(name, sourceCode) {
  var url = new URL('http://localhost:8080/lint');

  const params = {'name': name};

  url.search = new URLSearchParams(params);

  return fetch(url, {
    method: 'POST',
    mode: 'cors',
    headers: {
      'Accept': 'application/json',
      'Content-Type': 'text/plain', //evtl java spezifisch stattdessen?
    },
    body: sourceCode
  })
    .then((response) => response.json());
}

export default lint;