import brace from 'brace'

import 'brace/mode/java'

/**
 * Draft for a custom java mode. (not in use yet)
 * 
 * Based on information from:
 * 
 * - https://github.com/thlorenz/brace/issues/107
 * - https://github.com/ajaxorg/ace/wiki/Creating-or-Extending-an-Edit-Mode
 * - https://github.com/ajaxorg/ace/wiki/Syntax-validation
 * - https://himashag.blogspot.com/2016/10/creating-custom-mode-and-worker-files.html
 * - https://github.com/antlr/antlr4/blob/master/doc/ace-javascript-target.md
 *
 * For now, linting will be implemented by directly calling setAnnotations on the editor
 * session, since creating a worker is very work intensive, see last link.
 *
 */

brace.define('ace/mode/javaex', function(require, exports, module) {
  var oop = require("ace/lib/oop");

  // based on standard java mode
  var JavaMode = require("ace/mode/java").Mode;

  // based on standard java highlight rules (see below)
  var JavaExHighlightRules = require("ace/mode/javaex_highlight_rules").JavaExHighlightRules;

  var Mode = function() {
      this.HighlightRules = JavaExHighlightRules;
  };
  oop.inherits(Mode, JavaMode);

  (function() {
      // Extra mode logic
  }).call(Mode.prototype);

  exports.Mode = Mode;
});

brace.define('ace/mode/javaex_highlight_rules', function(require, exports, module) {
  var oop = require("ace/lib/oop");

  // based on existing ace java highlight rules
  var JavaHighlightRules = require("ace/mode/java_highlight_rules").JavaHighlightRules;

  var JavaExHighlightRules = function() {

      this.$rules = new JavaHighlightRules().getRules();
      
  }

  oop.inherits(JavaExHighlightRules, JavaHighlightRules);

  exports.JavaExHighlightRules = JavaExHighlightRules;
});
