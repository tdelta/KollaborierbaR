import ace from 'brace';
import 'brace/mode/java';
import './jml_highlighting.js';

ace.define('ace/mode/folding/jml',['require','exports','module','ace/lib/oop','ace/range','ace/mode/folding/fold_mode'], 
    function(acequire, exports, module) {
        'use strict';

        var oop = acequire('../../lib/oop');
        var Range = acequire('../../range').Range;
        var TokenIterator = acequire('ace/token_iterator').TokenIterator;

        var CStyleFoldMode = acequire('ace/mode/folding/cstyle').FoldMode;

        var FoldMode = exports.FoldMode = function(commentRegex) {
            if (commentRegex) {
                this.foldingStartMarker = new RegExp(
                    this.foldingStartMarker.source.replace(/\|[^|]*?$/, '|' + commentRegex.start)
                );
                this.foldingStopMarker = new RegExp(
                    this.foldingStopMarker.source.replace(/\|[^|]*?$/, '|' + commentRegex.end)
                );
            }
        };

        oop.inherits(FoldMode,CStyleFoldMode);

        (function() {
            
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
                        return _getCommentFoldRange(row,column,dir);
                    }
                };
		// Use the standard method for all other types (=CSS classes)
                return CStyleFoldMode.prototype.getFoldWidgetRange.call(this,session, foldStyle, row, forceMultiline);
            };
        }).call(FoldMode.prototype);
        exports.FoldMode = FoldMode;
    }
);

ace.define('ace/mode/jml',['require','exports','module','ace/lib/oop','ace/mode/javascript','ace/mode/java_highlight_rules'], function(acequire, exports, module) {
    'use strict';

    var oop = acequire('../lib/oop');
    var JavaScriptMode = acequire('./javascript').Mode;
    var JavaHighlightRules = acequire('ace/mode/java_highlight_rules').JavaHighlightRules;
    var JmlFoldMode = acequire('ace/mode/folding/jml').FoldMode;

    var Mode = function() {
        JavaScriptMode.call(this);
        this.HighlightRules = JavaHighlightRules;
        this.foldingRules = new JmlFoldMode();
    };
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
    }).call(Mode.prototype);

    exports.Mode = Mode;
});
