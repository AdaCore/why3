ace.define("ace/mode/why3_highlight_rules",["require","exports","module","ace/lib/oop","ace/mode/text_highlight_rules"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

var Why3HighlightRules = function() {

    var keywords = (
        "as|axiom|by|clone|coinductive|constant|" +
        "else|end|epsilon|exists|export|" +
        "false|float|forall|function|" +
        "goal|if|import|in|inductive|" +
        "lemma|let|match|meta|not|predicate|" +
        "range|scope|so|then|theory|true|type|use|with|" +
        // programs
        "abstract|any|at|" +
        "begin|break|continue|do|done|downto|exception|" +
        "for|fun|ghost|label|module|mutable|" +
        "old|private|pure|raise|rec|return|" +
        "to|try|val|while|" +
        // specification
        "absurd|alias|assert|assume|" +
        "check|diverges|ensures|invariant|" +
        "raises|reads|requires|returns|variant|writes"
    );

    var builtinConstants = ("true|false");

    var builtinFunctions = ("");

    var keywordMapper = this.createKeywordMapper({
        "variable.language": "this",
        "keyword": keywords,
        "constant.language": builtinConstants,
        "support.function": builtinFunctions
    }, "identifier");

    var decimalInteger = "(?:(?:[1-9]\\d*)|(?:0))";
    var octInteger = "(?:0[oO]?[0-7]+)";
    var hexInteger = "(?:0[xX][\\dA-Fa-f]+)";
    var binInteger = "(?:0[bB][01]+)";
    var integer = "(?:" + decimalInteger + "|" + octInteger + "|" + hexInteger + "|" + binInteger + ")";

    var exponent = "(?:[eE][+-]?\\d+)";
    var fraction = "(?:\\.\\d+)";
    var intPart = "(?:\\d+)";
    var pointFloat = "(?:(?:" + intPart + "?" + fraction + ")|(?:" + intPart + "\\.))";
    var exponentFloat = "(?:(?:" + pointFloat + "|" +  intPart + ")" + exponent + ")";
    var floatNumber = "(?:" + exponentFloat + "|" + pointFloat + ")";

    this.$rules = {
        "start" : [
            { token : [ "paren.lparen", "text", "paren.rparen" ],
              regex : "([(])([*])([)])"
            },
            {   //black magic from Rust mode to handle nested comments.
                token : "comment.start",
                regex : "\\(\\*",
                stateName : "comment",
                push : [
                    {
                        token: 'comment.start',
                        regex : "\\(\\*",
                        push : 'comment'
                    },
                    {
                        token: 'comment.end',
                        regex: "\\*\\)",
                        next: 'pop'
                    },
                    {
                        defaultToken: 'comment'
                    }
                ]
            },
            {
                token : "string", // single line
                regex : '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
            },
            {
                token : "string", // single char
                regex : "'.'"
            },
            {
                token : "string", // " string
                regex : '"',
                next  : "qstring"
            },
            {
                token : "constant.numeric", // float
                regex : floatNumber
            },
            {
                token : "constant.numeric", // integer
                regex : integer + "\\b"
            },
            {
                token : keywordMapper,
                regex : "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
            },
            {
                token : "keyword.operator",
                regex : "&&|\\|\\||/\\\\|\\\\/|->|<->"
            },
            {
                token : "paren.lparen",
                regex : "[[({]"
            },
            {
                token : "paren.rparen",
                regex : "[\\])}]"
            },
            {
                token : "text",
                regex : "\\s+"
            }
        ],
        "qstring" : [
            {
                token : "string",
                regex : '"',
                next : "start"
            }, {
                token : "string",
                regex : '[^"]'
            }
        ]
    };

    this.normalizeRules();
};

oop.inherits(Why3HighlightRules, TextHighlightRules);

exports.Why3HighlightRules = Why3HighlightRules;
});

ace.define("ace/mode/matching_brace_outdent",["require","exports","module","ace/range"], function(require, exports, module) {
"use strict";

var Range = require("../range").Range;

var MatchingBraceOutdent = function() {};

(function() {

    this.checkOutdent = function(line, input) {
        if (! /^\s+$/.test(line))
            return false;

        return /^\s*\}/.test(input);
    };

    this.autoOutdent = function(doc, row) {
        var line = doc.getLine(row);
        var match = line.match(/^(\s*\})/);

        if (!match) return 0;

        var column = match[1].length;
        var openBracePos = doc.findMatchingBracket({row: row, column: column});

        if (!openBracePos || openBracePos.row == row) return 0;

        var indent = this.$getIndent(doc.getLine(openBracePos.row));
        doc.replace(new Range(row, 0, row, column-1), indent);
    };

    this.$getIndent = function(line) {
        return line.match(/^\s*/)[0];
    };

}).call(MatchingBraceOutdent.prototype);

exports.MatchingBraceOutdent = MatchingBraceOutdent;
});

ace.define("ace/mode/why3",["require","exports","module","ace/lib/oop","ace/mode/text","ace/mode/why3_highlight_rules","ace/mode/matching_brace_outdent","ace/range"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var Why3HighlightRules = require("./why3_highlight_rules").Why3HighlightRules;
var MatchingBraceOutdent = require("./matching_brace_outdent").MatchingBraceOutdent;
var Range = require("../range").Range;

var Mode = function() {
    this.HighlightRules = Why3HighlightRules;

    this.$outdent   = new MatchingBraceOutdent();
};
oop.inherits(Mode, TextMode);

var indenter = /(?:[({[=:]|[-=]>|\b(?:else|try|with))\s*$/;

(function() {

    this.toggleCommentLines = function(state, doc, startRow, endRow) {
        var i, line;
        var outdent = true;
        var re = /^\s*\(\*(.*)\*\)/;

        for (i=startRow; i<= endRow; i++) {
            if (!re.test(doc.getLine(i))) {
                outdent = false;
                break;
            }
        }

        var range = new Range(0, 0, 0, 0);
        for (i=startRow; i<= endRow; i++) {
            line = doc.getLine(i);
            range.start.row  = i;
            range.end.row    = i;
            range.end.column = line.length;

            doc.replace(range, outdent ? line.match(re)[1] : "(*" + line + "*)");
        }
    };

    this.getNextLineIndent = function(state, line, tab) {
        var indent = this.$getIndent(line);
        var tokens = this.getTokenizer().getLineTokens(line, state).tokens;

        if (!(tokens.length && tokens[tokens.length - 1].type === 'comment') &&
            state === 'start' && indenter.test(line))
            indent += tab;
        return indent;
    };

    this.checkOutdent = function(state, line, input) {
        return this.$outdent.checkOutdent(line, input);
    };

    this.autoOutdent = function(state, doc, row) {
        this.$outdent.autoOutdent(doc, row);
    };
    this.blockComment = {start: "(*", end: "*)", nestable: true};
    this.$id = "ace/mode/why3";
}).call(Mode.prototype);

exports.Mode = Mode;
});
