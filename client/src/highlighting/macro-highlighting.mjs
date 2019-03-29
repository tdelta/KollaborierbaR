import ace from 'ace-builds';

ace.define( // create a new ace module
    'ace/mode/macro_highlight_rules', // it shall be available through this name
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
    const oop = acequire('ace/lib/oop');
    const TextHighlightRules = acequire('ace/mode/text_highlight_rules').TextHighlightRules;

    var MacroHighlightRules = function() {

        this.$rules = {
            start: [
              {
                token: 'keyword',
                regex: 'matches|auto|tryclose|select|branch|formula|number|rule|set|steps|breakpointscript|foreach|cases|case|matchLabel|matchSeq|closes|matchRule|repeat|theonly'
                // The regular expression matches all keywords. These shall be highlighted as 'keyword'
              }
            ]
        };
    }

    oop.inherits(MacroHighlightRules, TextHighlightRules);
    exports.MacroHighlightRules = MacroHighlightRules;
});
