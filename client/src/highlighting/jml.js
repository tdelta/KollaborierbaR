import brace from 'brace';
import 'brace/mode/java';
import './jml_highlighting.js';

// Defines how code in the editor can be folded. (This is used to generate the little arrows in the gutter)
// brace.define is used in order to import this somewhere else
brace.define('ace/mode/folding/jml',['require','exports','module','ace/lib/oop','ace/range','ace/mode/folding/fold_mode'], 
    function(acequire, exports, module) {
        'use strict';

        var oop = acequire('../../lib/oop');
        var Range = acequire('../../range').Range;
        var TokenIterator = acequire('ace/token_iterator').TokenIterator;

        var CStyleFoldMode = acequire('ace/mode/folding/cstyle').FoldMode;

	// Constructor from super class
        var FoldMode = exports.FoldMode = function(commentRegex) {
            CStyleFoldMode.constructor.call(this,commentRegex);
        };

        oop.inherits(FoldMode,CStyleFoldMode);

        (function() {

            // This function is called when a regular expression matches the start of foldable code.
            // It returns a range from start to end of that code that will be hidden
            this.getFoldWidgetRange = function(session, foldStyle, row, forceMultiline) {
                var _getCommentFoldRange = session.getCommentFoldRange.bind(session);
                // I changed this function because it works with the CSS "comment" class that we are not using
                session.getCommentFoldRange = function(row, column, dir){
                    var iterator = new TokenIterator(session, row, column);
                    var token = iterator.getCurrentToken();
                    var type = token.type;

                    if(type == 'jml_comment') {
                        var range = new Range();
                        range.start.row = iterator.getCurrentTokenRow();
                        range.start.column = iterator.getCurrentTokenColumn() + 3;
			// Look for the end of the comment block
                        while(token && !token.value.includes('@*/')){
                            token = iterator.stepForward();
                        }
			// End of comment wasnt found
			if(!token) return null;
                        range.end.row = iterator.getCurrentTokenRow();
                        range.end.column = iterator.getCurrentTokenColumn()+token.value.indexOf('@*/');
                        return range;
                    } else {
			// Use the standard method for all other types (=CSS classes)
                        return _getCommentFoldRange(row,column,dir);
                    }
                };
                return CStyleFoldMode.prototype.getFoldWidgetRange.call(this,session, foldStyle, row, forceMultiline);
            };
        // Calls the function in the context of FoldMode. That way we can write this instead of FoldMode.
        }).call(FoldMode.prototype);
        exports.FoldMode = FoldMode;
    }
);

// The JML Mode defined here combines folding, highlighting and indentation rules. This is what you have to import in order to use the JML Highlighting.
// ace.define is used in order to import this somewhere else
brace.define('ace/mode/jml',['require','exports','module','ace/lib/oop','ace/mode/javascript','ace/mode/java_highlight_rules'], function(acequire, exports, module) {
    'use strict';

    // acequire imports ace modules
    var oop = acequire('../lib/oop');
    var JavaScriptMode = acequire('./javascript').Mode;
    var JavaHighlightRules = acequire('ace/mode/java_highlight_rules').JavaHighlightRules;
    var JmlFoldMode = acequire('ace/mode/folding/jml').FoldMode;

    // Constructor of the JML mode
    var Mode = function() {
        JavaScriptMode.call(this);
        this.HighlightRules = JavaHighlightRules;
        this.foldingRules = new JmlFoldMode();
    };
    // Extend the Javascript mode
    oop.inherits(Mode, JavaScriptMode);

    (function() {
        
        this.createWorker = function(session) {
            return null;
        };

        // Creates the beginning of a new line when the user presses enter
        this.getNextLineIndent = function(state, line, tab){
            if(state == 'jml-block-comment'){
                // Count the characters in front of the first '@' in the current line
                var indent = line.match(/[^@]+/).toString().length;
                // Create a string of indent whitespaces and an @
                return Array(indent+1).join(' ')+'@';
            } else {
                // Use the indentation rules from the JavascriptMode (= JavaMode)
                return JavaScriptMode.prototype.getNextLineIndent.call(this,state,line,tab);
            }
        };
        
        this.$id = 'ace/mode/jml';
    // Calls the function in the context of Mode.prototype. That way we can write this instead of Mode.
    }).call(Mode.prototype);

    exports.Mode = Mode;
});
