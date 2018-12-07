import ace from 'ace-builds';
import './jml_highlighting.js';

/**
 * This highlighting module is identical to the standard java highlighting
 * module of ace, but with JML rules added.
 *
 * Everything else is unchanged.
 */
ace.define( // we tell ace, that we want to define our own ace extension module
    'ace/mode/custom_java_highlight_rules', // it shall be available at this (virtual) import path
    // we will use these ace internal helper functions and modules.
    // Therefore we will tell ace here, that we depend on them:
    [
        'require', // we want to be able to load other ace modules
        'exports', // we want to export our own functionality
        'module',
        'ace/lib/oop', // we want OOP functionality (inheriting from existing ace modes, etc.)
        'ace/mode/doc_comment_highlight_rules', // the java highlight rules use doc_comment_highlight_rules
        'ace/mode/jml_highlight_rules', // we want to import our jml_highlight_rules
        'ace/mode/text_highlight_rules' // this is the base function for text highlighting
    ], function(acequire, exports, module) {

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
                    // The JavaMode had to be changed here to insert jml comments
                    // into the start state.
                    JmlHighlightRules.getStartRule('jml-specs'),
                    {
                        token : 'comment',
                        regex : '\\/\\/.*$'
                    },
                    JmlBlockHighlightRules.getStartRule('jml-block-specs'),
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

            // embedRules adds the remaining grammar rules. It adds the endRule to every state of our newly added rules and prefixes the new rules with the second argument (jml-).
            this.embedRules(JmlHighlightRules,'jml-',
                [ JmlHighlightRules.getEndRule('start') ]);

            this.embedRules(JmlBlockHighlightRules,'jml-',
                [ JmlBlockHighlightRules.getEndRule('start') ]);

            this.embedRules(DocCommentHighlightRules, 'doc-',
                [ DocCommentHighlightRules.getEndRule('start') ]);
        };
        // All highlighting rules extend TextHighlightRules
        oop.inherits(JavaHighlightRules, TextHighlightRules);
        exports.JavaHighlightRules = JavaHighlightRules;
    }
);
