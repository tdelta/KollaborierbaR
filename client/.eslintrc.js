module.exports = {
    "parser": "babel-eslint",
    "env": {
        "browser": true,
        "es6": true,
        // support test files
        "jest": true
    },
    "plugins": ["prettier"],
    "extends": [
      "eslint:recommended",
      "plugin:react/recommended",
      "prettier",
      "prettier/react"
    ],
    "parserOptions": {
        "ecmaFeatures": {
            "jsx": true
        },
        "ecmaVersion": 2018,
        "sourceType": "module"
    },
    "settings": {
        "react":{
            "version": "15.0",
        },
    },
    "rules": {
        "prettier/prettier": "error",
        "linebreak-style": [
            "error",
            "unix"
        ],
        "quotes": [
            "error",
            "single"
        ],
        // unused function arguments shall be no error
        "no-unused-vars": ["error", { "args": "none" }],
        "no-console": "off"
    }
};
