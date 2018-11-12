module.exports = {
    "env": {
        "browser": true,
        "es6": true,
        // support test files
        "jest": true
    },
    "extends": [
      "eslint:recommended",
    ],
    "parserOptions": {
        "ecmaFeatures": {
            "jsx": true
        },
        "ecmaVersion": 2018,
        "sourceType": "module"
    },
    "plugins": [
        "react"
    ],
    "rules": {
        "indent": [
            "error",
            4,
            {
                // switch bodies shall be indented
                "SwitchCase": 1,
            }
        ],
        "linebreak-style": [
            "error",
            "unix"
        ],
        "quotes": [
            "error",
            "single"
        ],
        "semi": [
            "error",
            "always"
        ],
        // unused function arguments shall be no error
        "no-unused-vars": ["error", { "args": "none" }],
        // prevent false positives in react code (due to JSX extensions)
        "react/jsx-uses-react": "error",   
        "react/jsx-uses-vars": "error" 
    }
};
