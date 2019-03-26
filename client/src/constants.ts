// Contains application wide constants

declare var staticConfiguration: { serverAddress: string };

export const serverAddress: string = staticConfiguration.serverAddress;

// names of server routes. Can be used to construct urls for calls to fetch()
export const serverRoutes: object = {
  projects: {
    openFile: '/projects/openFile',
  },
};
