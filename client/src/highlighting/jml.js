import ace from 'brace';
import 'brace/mode/java';

ace.define('ace/mode/jml_highlight_rules',['require','exports','module','ace/lib/oop','ace/mode/text_highlight_rules'],
    function(acequire, exports, module) {
        'use strict';

        var oop = acequire('../lib/oop');
        var lang = acequire('../lib/lang');
        var TextHighlightRules = acequire('./text_highlight_rules').TextHighlightRules;

        var behavior_keyword = lang.arrayToMap(
            ('behavior|normal_behavior|exceptional_behavior|behaviour|normal_behaviour|exceptional_behaviour').split('|'));
        var java_visibility_keyword = lang.arrayToMap(
            ('public|protected|private').split('|'));
        var requires_keyword = lang.arrayToMap(
            ('requires|pre|requires_redundantly|pre_redundantly').split('|'));
        var ensures_keyword = lang.arrayToMap(
            ('ensures|post|ensures_redundantly|post_redundantly').split('|'));
        var signals_keyword = lang.arrayToMap(
            ('signals|signals_redundantly|exsures|exsures_redundantly').split('|'));
        var signals_only_keyword = lang.arrayToMap(
            ('signals_only|signals_only_redundantly').split('|'));
        var diverges_keyword = lang.arrayToMap(
            ('diverges|diverges_redundantly').split('|'));
        var when_keyword = lang.arrayToMap(
            ('when|when_redundantly').split('|'));
        var assignable_keyword = lang.arrayToMap(
            ('assignable|assignable_redundantly|modifiable|modifiable_redundantly|modifies|modifies_redundantly').split('|'));
        var accessible_keyword = lang.arrayToMap(
            ('accessible|accessible_redundantly').split('|'));
        var callable_keyword = lang.arrayToMap(
            ('callable|callable_redundantly').split('|'));
        var measured_by_keyword = lang.arrayToMap(
            ('measured_by|measured_by_redundantly').split('|'));
        var captures_keyword = lang.arrayToMap(
            ('captures|captures_redundantly').split('|'));
        var working_space_keyword = lang.arrayToMap(
            ('working_space|working_space_redundantly').split('|'));
        var duration_keyword = lang.arrayToMap(
            ('duration|duration_redundantly').split('|'));
        var predicate_keyword = lang.arrayToMap(
            ('\\TYPE|\\bigint|\\bigint_math|\\duration|\\elemtype|\\everything|\\exists|\\forall|\\fresh|\\into|\\invariant_for|\\is_initialized|\\java_math|\\lblneg|\\lblpos|'+
            '\\lockset|\\max|\\min|\\nonnullelements|\\not_assigned|\\not_modified|\\not_specified|\\nothing|\\nowarn|\\nowarn_op|\\num_of|\\old|\\only_accessed|\\only_assigned|'+
            '\\only_called|\\only_captured|\\pre|\\product|\\reach|\\real|\\result|\\same|\\safe_math|\\space|\\such_that|\\sum|\\typeof|\\type|\\warn_op|\\warn|\\working_space').split('|'));
        var other_keyword=lang.arrayToMap('abrupt_behavior|abrupt_behaviour|also|assert_redundantly|assume|assume_redundantly|axiom|breaks|breaks_redundantly|choose|choose_if|code|code_bigint_math||code_java_math|code_safe_math|constraint|constraint_redundantly|constructor|continues|continues_redundantly|decreases|decreases_redundantly|decreasing|decreasing_redundantly|example|exceptional_example|extract|field|forall|for_example|ghost|helper|hence_by|hence_by_redundantly|implies_that|in|in_redundantly|initializer|initially|instance|invariant|invariant_redundantly|loop_invariant|loop_invariant_redundantly|maintaining|maintaining_redundantly|maps|maps_redundantly|method|model|model_program|monitored|monitors_for|non_null|normal_example|nowarn|nullable|nullable_by_default|old|or|pure|readable|refining|represents|represents_redundantly|returns|returns_redundantly|set|signals_only|signals_only_redundantly|spec_bigint_math|spec_java_math|spec_protected|spec_public|spec_safe_math|static_initializer|uninitialized|unreachable|writable'.split('|'));
        var special_symbol=lang.arrayToMap('===>|<==|<==>|<=!=>|->|<-|<:|..|`{|\'|`|}\'|<#|<#='.split('|'));

        var keywords = function(value) {
            if(behavior_keyword.hasOwnProperty(value)) return 'keyword';
            if(java_visibility_keyword.hasOwnProperty(value)) return 'keyword';
            if(requires_keyword.hasOwnProperty(value)) return 'keyword';
            if(ensures_keyword.hasOwnProperty(value)) return 'keyword';
            if(signals_keyword.hasOwnProperty(value)) return 'keyword';
            if(signals_only_keyword.hasOwnProperty(value)) return 'keyword';
            if(diverges_keyword.hasOwnProperty(value)) return 'keyword';
            if(when_keyword.hasOwnProperty(value)) return 'keyword';
            if(assignable_keyword.hasOwnProperty(value)) return 'keyword';
            if(accessible_keyword.hasOwnProperty(value)) return 'keyword';
            if(callable_keyword.hasOwnProperty(value)) return 'keyword';
            if(measured_by_keyword.hasOwnProperty(value)) return 'keyword';
            if(captures_keyword.hasOwnProperty(value)) return 'keyword';
            if(working_space_keyword.hasOwnProperty(value)) return 'keyword';
            if(duration_keyword.hasOwnProperty(value)) return 'keyword';
            if(predicate_keyword.hasOwnProperty(value)) return 'keyword';
            if(other_keyword.hasOwnProperty(value)) return 'keyword';
            return 'jml_comment';
        };

        var symbols = function(value) {
            if(special_symbol.hasOwnProperty(value)) return 'text';
            return 'jml_comment';
        };

        var JmlHighlightRules = function() {
            this.$rules = {
                'comment' : [
                    {
                        token : (value) => keywords(value),
                        regex : /\\?\w+/,
                    },
                    {
                        token : (value) => symbols(value),
                        regex : /[#|<|>|=|:|!|.|{|}|`|']+/,
                    },
                    {
                        defaultToken : 'jml_comment',
                    },
                ],
            };
        };

        var JmlBlockHighlightRules = function() {
            this.$rules = {
                'block-comment' : [
                    {
                        token: (value) => keywords(value),
                        regex: /\\?\w+/,
                    },
                    {
                        token : (value) => symbols(value),
                        regex : /[#|<|>|=|:|!|.|{|}|`|']+/,
                    }, {
                        defaultToken : 'jml_comment'
                    }
                ]
            };
        };

        JmlBlockHighlightRules.getStartRule = function(start) {
            return{
                token : 'jml_comment',
                regex : /\/\*@/,
                next: start,
            };
        };

        JmlHighlightRules.getStartRule = function(start) {
            return{
                token : 'jml_comment',
                regex : /\/\/@/,
                next: start,
            };
        };

        JmlHighlightRules.getEndRule = function(start) {
            return{
                token : 'jml_comment',
                regex : '$',
                next : 'start',
            };
        };

        JmlBlockHighlightRules.getEndRule = function(start) {
            return{
                token : 'jml_comment',
                regex : /\*\//,
                next : start,
            };
        };

        oop.inherits(JmlHighlightRules, TextHighlightRules);
        oop.inherits(JmlBlockHighlightRules, TextHighlightRules);

        exports.JmlHighlightRules = JmlHighlightRules;
        exports.JmlBlockHighlightRules = JmlBlockHighlightRules;
    }
);

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
            
            this.foldingStartMarker = /([{[(])[^}\])]*$|^\s*(\/\*)/;
            this.foldingStopMarker = /^[^[{(]*([}\])])|^[\s*]*(\*\/)/;
            this.singleLineBlockCommentRe= /^\s*(\/\*).*\*\/\s*$/;
            this.tripleStarBlockCommentRe = /^\s*(\/\*\*\*).*\*\/\s*$/;
            this.startRegionRe = /^\s*(\/\*|\/\*\*\*|\/\/)#?region\b/;



            this.getFoldWidgetRange = function(session, foldStyle, row, forceMultiline) {
                var _getCommentFoldRange = session.getCommentFoldRange.bind(session);
                // Die Funktion habe ich geändert, da sie mit der CSS "comment" Klasse arbeitet, die hier nicht genutzt wurde
                session.getCommentFoldRange = function(row, column, dir){
                    var iterator = new TokenIterator(session, row, column);
                    var token = iterator.getCurrentToken();
                    var type = token.type;

                    if(type == 'jml_comment') {
                        var range = new Range();
                        range.start.row = iterator.getCurrentTokenRow();
                        range.start.column = iterator.getCurrentTokenColumn() + 3;
                        while(token && !token.value.includes('@*/')){
                            token = iterator.stepForward();
                        }
                        range.end.row = iterator.getCurrentTokenRow();
                        range.end.column = iterator.getCurrentTokenColumn()+token.value.indexOf('@*/');
                        return range;
                    } else {
                        return _getCommentFoldRange(row,column,dir);
                    }
                };
                return CStyleFoldMode.prototype.getFoldWidgetRange.call(this,session, foldStyle, row, forceMultiline);
            };
        }).call(FoldMode.prototype);
        exports.FoldMode = FoldMode;
    }
);

ace.define('ace/mode/java_highlight_rules',['require','exports','module','ace/lib/oop','ace/mode/doc_comment_highlight_rules','ace/mode/jml_highlight_rules','ace/mode/text_highlight_rules'], function(acequire, exports, module) {
    'use strict';

    var oop = acequire('../lib/oop');
    var DocCommentHighlightRules = acequire('./doc_comment_highlight_rules').DocCommentHighlightRules;
    var JmlHighlightRules = acequire('./jml_highlight_rules').JmlHighlightRules;
    var JmlBlockHighlightRules = acequire('./jml_highlight_rules').JmlBlockHighlightRules;
    var TextHighlightRules = acequire('./text_highlight_rules').TextHighlightRules;

    var JavaHighlightRules = function() {
        var keywords = (
            'abstract|continue|for|new|switch|' +
            'assert|default|goto|package|synchronized|' +
            'boolean|do|if|private|this|' +
            'break|double|implements|protected|throw|' +
            'byte|else|import|public|throws|' +
            'case|enum|instanceof|return|transient|' +
            'catch|extends|int|short|try|' +
            'char|final|interface|static|void|' +
            'class|finally|long|strictfp|volatile|' +
            'const|float|native|super|while'
        );

        var buildinConstants = ('null|Infinity|NaN|undefined');


        var langClasses = (
            'AbstractMethodError|AssertionError|ClassCircularityError|'+
            'ClassFormatError|Deprecated|EnumConstantNotPresentException|'+
            'ExceptionInInitializerError|IllegalAccessError|'+
            'IllegalThreadStateException|InstantiationError|InternalError|'+
            'NegativeArraySizeException|NoSuchFieldError|Override|Process|'+
            'ProcessBuilder|SecurityManager|StringIndexOutOfBoundsException|'+
            'SuppressWarnings|TypeNotPresentException|UnknownError|'+
            'UnsatisfiedLinkError|UnsupportedClassVersionError|VerifyError|'+
            'InstantiationException|IndexOutOfBoundsException|'+
            'ArrayIndexOutOfBoundsException|CloneNotSupportedException|'+
            'NoSuchFieldException|IllegalArgumentException|NumberFormatException|'+
            'SecurityException|Void|InheritableThreadLocal|IllegalStateException|'+
            'InterruptedException|NoSuchMethodException|IllegalAccessException|'+
            'UnsupportedOperationException|Enum|StrictMath|Package|Compiler|'+
            'Readable|Runtime|StringBuilder|Math|IncompatibleClassChangeError|'+
            'NoSuchMethodError|ThreadLocal|RuntimePermission|ArithmeticException|'+
            'NullPointerException|Long|Integer|Short|Byte|Double|Number|Float|'+
            'Character|Boolean|StackTraceElement|Appendable|StringBuffer|'+
            'Iterable|ThreadGroup|Runnable|Thread|IllegalMonitorStateException|'+
            'StackOverflowError|OutOfMemoryError|VirtualMachineError|'+
            'ArrayStoreException|ClassCastException|LinkageError|'+
            'NoClassDefFoundError|ClassNotFoundException|RuntimeException|'+
            'Exception|ThreadDeath|Error|Throwable|System|ClassLoader|'+
            'Cloneable|Class|CharSequence|Comparable|String|Object'
        );

        var keywordMapper = this.createKeywordMapper({
            'variable.language': 'this',
            'keyword': keywords,
            'constant.language': buildinConstants,
            'support.function': langClasses
        }, 'identifier');

        this.$rules = {
            'start' : [
                JmlHighlightRules.getStartRule('jml-comment'),
                {
                    token : 'comment',
                    regex : '\\/\\/.*$'
                },
                JmlBlockHighlightRules.getStartRule('jml-block-comment'),
                DocCommentHighlightRules.getStartRule('doc-start'),
                {
                    token : 'comment', // multi line comment
                    regex : '\\/\\*',
                    next : 'test-comment'
                }, {
                    token : 'string', // single line
                    regex : '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
                }, {
                    token : 'string', // single line
                    regex : '[\'](?:(?:\\\\.)|(?:[^\'\\\\]))*?[\']'
                }, {
                    token : 'constant.numeric', // hex
                    regex : /0(?:[xX][0-9a-fA-F][0-9a-fA-F_]*|[bB][01][01_]*)[LlSsDdFfYy]?\b/
                }, {
                    token : 'constant.numeric', // float
                    regex : /[+-]?\d[\d_]*(?:(?:\.[\d_]*)?(?:[eE][+-]?[\d_]+)?)?[LlSsDdFfYy]?\b/
                }, {
                    token : 'constant.language.boolean',
                    regex : '(?:true|false)\\b'
                }, {
                    token : keywordMapper,
                    regex : '[a-zA-Z_$][a-zA-Z0-9_$]*\\b'
                }, {
                    token : 'keyword.operator',
                    regex : '!|\\$|%|&|\\*|\\-\\-|\\-|\\+\\+|\\+|~|===|==|=|!=|!==|<=|>=|<<=|>>=|>>>=|<>|<|>|!|&&|\\|\\||\\?\\:|\\*=|%=|\\+=|\\-=|&=|\\^=|\\b(?:in|instanceof|new|delete|typeof|void)'
                }, {
                    token : 'lparen',
                    regex : '[[({]'
                }, {
                    token : 'rparen',
                    regex : '[\\])}]'
                }, {
                    token : 'text',
                    regex : '\\s+'
                }
            ],
            'test-comment' : [
                {
                    token : 'comment', // closing comment
                    regex : '\\*\\/',
                    next : 'start'
                }, {
                    defaultToken : 'comment'
                }
            ]
        };


        this.embedRules(JmlHighlightRules,'jml-',
            [ JmlHighlightRules.getEndRule('start') ]);

        this.embedRules(JmlBlockHighlightRules,'jml-',
            [ JmlBlockHighlightRules.getEndRule('start') ]);

        this.embedRules(DocCommentHighlightRules, 'doc-',
            [ DocCommentHighlightRules.getEndRule('start') ]);
    };

    oop.inherits(JavaHighlightRules, TextHighlightRules);

    exports.JavaHighlightRules = JavaHighlightRules;
});

ace.define('ace/mode/jml',['require','exports','module','ace/lib/oop','ace/mode/javascript','ace/mode/java_highlight_rules'], function(acequire, exports, module) {
    'use strict';

    var oop = acequire('../lib/oop');
    var JavaScriptMode = acequire('./javascript').Mode;
    var JavaHighlightRules = acequire('./java_highlight_rules').JavaHighlightRules;
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

        this.getNextLineIndent = function(state, line, tab){
            if(state == 'jml-block-comment'){
                // Zähle die Character vor dem ersten @ in der Zeile
                var indent = line.match(/[^@]+/).toString().length;
                // Indentation der nächsten Zeile in Whitespace mit @ am Ende
                return Array(indent+1).join(' ')+'@';
            } else {
                // Nutze die Indentation rules aus dem JavaScriptMode (bzw Java Mode)
                return JavaScriptMode.prototype.getNextLineIndent.call(this,state,line,tab);
            }
        };
        
        this.$id = 'ace/mode/jml';
    }).call(Mode.prototype);

    exports.Mode = Mode;
});
