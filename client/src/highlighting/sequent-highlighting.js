import ace from 'ace-builds';
import './java-ex-highlighting.js';

ace.define( // create a new ace module
    'ace/mode/sequent_highlight_rules', // it shall be available through this name
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
    const JavaExHighlightRules = acequire('ace/mode/custom_java_highlight_rules').JavaHighlightRules;
    const lang = acequire('../lib/lang');
    
    var SequentHighlightRules = function() {

        let keywords = lang.arrayToMap([
          'measuredByEmpty',
          'wellFormed'
        ]);

        let literals = lang.arrayToMap([
          'TRUE',
          'FALSE',
          'null',
          'heap'
        ]);

        let identifyKeywords = function(word){
          if(keywords.hasOwnProperty(word)) return 'keyword';
          else if(literals.hasOwnProperty(word)) return 'constant.language';
          else return 'text';
        }
    
        this.$rules = {
          'start':[
            {
              token : (value) => identifyKeywords(value),
              // Regular expression matches all words made of characters and possibly starting with \
              regex : /\\?\w+/,
            },
            {
              token:'operator',
              regex:'\\<|\\[',
              next: 'method-frame'
            }
          ],
          'method-frame':[
            {
              token : (value) => identifyKeywords(value),
              // Regular expression matches all words made of characters and possibly starting with \
              regex : /\\?\w+/,
            },
            {
              token:'operator',
              regex:':',
              next: 'java-ex-start'
            }
          ]
        };

        let javaEndRule = {
          token: 'operator',
          regex:'\\>|\\]',
          next: 'start'
        };

        // embedRules adds the remaining grammar rules. It adds the endRule to every state of our newly added rules and prefixes the new rules with the second argument (java-ex-).
        this.embedRules(JavaExHighlightRules,'java-ex-',
            [ javaEndRule ]);
    };
 
    oop.inherits(SequentHighlightRules, TextHighlightRules);
    
    exports.SequentHighlightRules = SequentHighlightRules;
});
