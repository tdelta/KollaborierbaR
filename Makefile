CLIENT_DIR = client
SERVER_DIR = linting-server

# indicate, that submodules are not files
.PHONY: setup client linter clean

all: linter client

setup:
	$(MAKE) -C $(CLIENT_DIR) setup
	$(MAKE) -C $(SERVER_DIR) setup

# build instructions for submodules
client:
	$(MAKE) -C $(CLIENT_DIR)

server:
	$(MAKE) -C $(SERVER_DIR)

clean:
	$(MAKE) -C $(CLIENT_DIR) clean
	$(MAKE) -C $(SERVER_DIR) clean


