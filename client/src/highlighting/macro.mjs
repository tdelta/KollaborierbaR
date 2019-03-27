import ace from 'ace-builds';
import './macro-highlighting.mjs';

// Define a module that can be required by ace later on
ace.define(
    'ace/mode/macro',
    function(acequire, exports, module) {
        // acequire imports ace modules
        var oop = acequire('../lib/oop');
        var TextMode = acequire('ace/mode/text').Mode;
        var HighlightRules = acequire('ace/mode/macro_highlight_rules').MacroHighlightRules;

        var Mode = function(){
          // Use the syntax highlighting defined in macro-highlighting.mjs
          this.HighlightRules = HighlightRules;
        }

        oop.inherits(Mode,TextMode);
        exports.Mode = Mode;
    }
);
