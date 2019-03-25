import ace from 'ace-builds';
import './jml.js';
import './sequent-highlighting.js';

/**
 * The JML Mode defined here combines folding, highlighting and indentation
 * rules for java + jml + sequents.
 *
 * This is what you have to import in order to use the sequent highlighting and
 * retain all other java editor features.
 */
ace.define('ace/mode/sequent', function(acequire, exports, module) {
  // acequire imports ace modules
  var oop = acequire('../lib/oop');
  var JmlMode = acequire('./jml').Mode;
  var SequentHighlightRules = acequire('ace/mode/sequent_highlight_rules')
    .SequentHighlightRules;

  // Constructor of the JML mode
  var Mode = function() {
    JmlMode.call(this);
    this.HighlightRules = SequentHighlightRules;
  };
  // Extend the Javascript mode
  oop.inherits(Mode, JmlMode);

  (function() {
    this.$id = 'ace/mode/jml';
    // Calls the function in the context of Mode.prototype. That way we can write this instead of Mode.
  }.call(Mode.prototype));

  exports.Mode = Mode;
});
