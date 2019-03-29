// Contains application wide constants

declare var staticConfiguration: {
  serverAddress?: string,
  permanentEditHighlighting?: false,
} | undefined;

/**
 * Build app configuration from external config file (config.js) and default
 * values.
 *
 * Replaces configuration values with default ones, whenever it is not
 * externally configured.
 */
const activeConfig = (() => {
  const defaultConfig = {
    serverAddress: 'http://localhost:9000',
    permanentEditHighlighting: false,
  };

  if (staticConfiguration != null) {
    return {
      serverAddress: staticConfiguration.serverAddress != null ?
        staticConfiguration.serverAddress : defaultConfig.serverAddress,
      permanentEditHighlighting: staticConfiguration.permanentEditHighlighting != null ?
        staticConfiguration.permanentEditHighlighting : defaultConfig.permanentEditHighlighting
    };
  }

  else {
    return defaultConfig;
  }
})();

export const serverAddress: string = activeConfig.serverAddress;
export const permanentEditHighlighting: boolean = activeConfig.permanentEditHighlighting;

// names of server routes. Can be used to construct urls for calls to fetch()
export const serverRoutes: object = {
  projects: {
    openFile: '/projects/openFile',
  },
};
