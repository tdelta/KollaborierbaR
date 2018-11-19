import brace from 'brace';

import getSyntax from './jml-syntax.js';
import './java-ex-highlighting.js';

/**
 * Highlighting rules ace module for JML.
 *
 * We extracted the keywords from here:
 * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_22.html<Paste>
 */
brace.define( // create a new ace module
    'ace/mode/jml_highlight_rules', // it shall be available through this name
    // we will use these ace internal helper functions and modules.
    // Therefore we will tell ace here, that we depend on them:
    [ 
        'require', // we want to be able to load other ace modules
        'exports', // we want to export our own functionality
        'module',
        'ace/lib/oop', // we want OOP functionality (inheriting from existing ace modes, etc.)
        'ace/mode/text_highlight_rules' // we will include the existing basic highlight rules
    ],
    function(acequire, exports) {
        // we want OOP functionality (inheriting from existing ace modes, etc.)
        const oop = acequire('../lib/oop');
        // the lang module will provide use with `arrayToMap`, see below
        const lang = acequire('../lib/lang');
        // we will include the existing basic highlight rules
        const TextHighlightRules = acequire('./text_highlight_rules').TextHighlightRules;

        // get syntax information: Keyword list, operators etc.
        const syntax = getSyntax(lang);

        // Identifies, whether a given value is a special keyword, or just a regular
        // part of a jml comment
        const identifyKeywords = (value) => {
            for (const keywordClass in Object.assign(syntax.keywords,syntax.types)) {
                // check whether the value is contained in the current keyword class
                if (syntax.keywords[keywordClass].hasOwnProperty(value)) {
                    return 'keyword';
                }
            }

            return 'jml_comment';
        };

        // Checks, whether a given value is a special JML symbol or
        // operator
        const identifySymbols = (value) => {
            if(syntax.special_symbols.hasOwnProperty(value)) return 'text';
            if(syntax.operators.hasOwnProperty(value)) return 'text';
            return 'jml_comment';
        };

        // The grammar rules try to match regular expressions over the whole text in the editor and return tokens that will be used to generate CSS classes. If a rule has a state attribute, the specified state will be used after the regular expression was matched.
        const JmlHighlightRules = function() {
            this.$rules = {
                'comment' : [
                    {
                        token : (value) => identifyKeywords(value),
                        // Regular expression matches all words made of characters and possibly starting with \
                        regex : /\\?\w+/,
                    },
                    {
                        token : (value) => identifySymbols(value),
                        // Regular expression matches all strings of special characters
                        regex : /[#|<|>|=|:|!|.|{|}|`|'|||&|*|+|-]+/,
                    },
                    {
                        defaultToken : 'jml_comment',
                    },
                ],
            };
        };

        // We used seperate rules for comment blocks and single line comments because they have seperate end conditions that should lead into the start state of the java highlighting rules.
        var JmlBlockHighlightRules = function() {
            this.$rules = {
                'block-comment' : [
                    {
                        token: (value) => identifyKeywords(value),
                        regex: /\\?\w+/,
                    },
                    {
                        token : (value) => identifySymbols(value),
                        regex : /[#|<|>|=|:|!|.|{|}|`|'|||&|*|+|-]+/,
                    }, {
                        defaultToken : 'jml_comment'
                    }
                ]
            };
        };

        JmlBlockHighlightRules.getStartRule = function(start) {
            // Generates a rule that goes into the state specified in start, when /*@ is found.
            return{
                token : 'jml_comment',
                regex : /\/\*@/,
                next: start,
            };
        };

        JmlHighlightRules.getStartRule = function(start) {
            // Generates a rule that goes into the start state, when //@ is found.
            return{
                token : 'jml_comment',
                regex : /\/\/@/,
                next: start,
            };
        };

        JmlHighlightRules.getEndRule = function(start) {
            // Generates a rule that goes into the (JavaHighlight-) start state, when a line end is found
            return{
                token : 'jml_comment',
                regex : '$',
                next : start,
            };
        };

        JmlBlockHighlightRules.getEndRule = function(start) {
            // Generates a rule that goes into the (JavaHighlight-) start state, when */ is found
            return{
                token : 'jml_comment',
                regex : /\*\//,
                next : start,
            };
        };

        // stack custom jml rules on top of standard rules and export them
        // so that they are available in the editor
        oop.inherits(JmlHighlightRules, TextHighlightRules);
        oop.inherits(JmlBlockHighlightRules, TextHighlightRules);

        exports.JmlHighlightRules = JmlHighlightRules;
        exports.JmlBlockHighlightRules = JmlBlockHighlightRules;
    }
);
