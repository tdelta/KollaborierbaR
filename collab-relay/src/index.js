const io = require('socket.io')();
io.set('origins', '*:*'); // allow Cross-Origin requests

io.on('connection', client => {
  client.on('operation', op => {
    io.sockets.emit('operation', op); // just broadcast every incoming message to all clients
  });
});

io.listen(3001);
