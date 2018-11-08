CLIENT_DIR = client
SERVER_DIR = linting-server

# indicate, that submodules are not files
.PHONY: setup check client linter test clean

all: server client

# install dependencies etc.
setup:
	$(MAKE) -C $(CLIENT_DIR) setup
	$(MAKE) -C $(SERVER_DIR) setup

# run static analysis tools
check:
	$(MAKE) -C $(CLIENT_DIR) check
	$(MAKE) -C $(SERVER_DIR) check

# build
client:
	$(MAKE) -C $(CLIENT_DIR)

server:
	$(MAKE) -C $(SERVER_DIR)

# run unit tests
test:
	$(MAKE) -C $(CLIENT_DIR) test
	$(MAKE) -C $(SERVER_DIR) test

clean:
	$(MAKE) -C $(CLIENT_DIR) clean
	$(MAKE) -C $(SERVER_DIR) clean


