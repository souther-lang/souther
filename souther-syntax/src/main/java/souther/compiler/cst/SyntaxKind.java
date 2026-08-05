package souther.compiler.cst;

import souther.compiler.diag.Localizable;

import java.util.Locale;

/**
 * The single kind space of the concrete syntax tree: leaf (token) kinds, trivia kinds, and
 * internal node kinds, all in one enum (the rowan/Roslyn model). A {@link GreenToken} carries a
 * leaf or trivia kind; a {@link GreenNode} carries an internal-node kind.
 *
 * <p>Unlike the compiler's older {@code TokenType}, this space also names whitespace and comments
 * (trivia), so the tree is lossless — concatenating every leaf's text reproduces the source
 * exactly. That invariant is what the formatter and incremental reparse rest on.
 */
public enum SyntaxKind {
    // --- trivia (kept in the tree; skipped by the parser's token cursor) ---
    WHITESPACE,
    LINE_COMMENT,

    // --- keywords ---
    // `example` / `examples` / `for` are NOT reserved (they would collide with the `example.*`
    // package/module names): the parser recognizes them by text at top-level position, like the
    // contextual `intrinsic` / `decoder` / `from`. `on`, the second word of `depends on`, is read
    // the same way, so a field or parameter may still be named on.
    MODULE_KW, IMPORT_KW, EXPOSING_KW, DATA_KW, INVARIANT_KW, AS_KW, LET_KW, GUARD_KW, ELSE_KW,
    TRUE_KW, FALSE_KW, IF_KW, THEN_KW, BEHAVIOR_KW, DEPENDS_KW, CONSTRUCTS_KW, MATCH_KW, WITH_KW,
    UNREACHABLE_KW,

    // --- literals and identifiers ---
    IDENT, INT_LIT, DECIMAL_LIT, STRING_LIT, TYPEVAR,

    // --- punctuation ---
    LBRACE, RBRACE, LPAREN, RPAREN, LBRACKET, RBRACKET, COLON, COMMA, DOT, SPREAD, ASSIGN, PIPE,
    ARROW, LARROW, PIPEFWD, VPIPE, QUESTION, PLUSPLUS,

    // --- operators ---
    EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH,

    // --- end of input / lexical error ---
    EOF, ERROR_TOKEN,

    // --- nodes: top level ---
    SOURCE_FILE,
    MODULE_HEADER,
    EXPOSING_CLAUSE,
    EXPOSED_ENTRY,
    IMPORT_DECL,
    IMPORT_ALIAS,       // `as B` on an import: the qualifier this module reads the module under
    NAME_LIST,          // parenthesised comma list of names (import/exposing bodies)
    QUALIFIED_NAME,     // dotted module or member name

    // --- nodes: data ---
    DATA_DEF,
    PRODUCT_BODY,
    FIELD,
    SPREAD_MEMBER,
    SUM_BODY,
    NEWTYPE_BODY,
    INVARIANT_CLAUSE,

    // --- nodes: behavior ---
    BEHAVIOR_DEF,
    BEHAVIOR_SIG,
    PIPE_BEHAVIOR,
    PARAM_LIST,
    PARAM,
    CONSTRUCTS_CLAUSE,
    DEPENDS_CLAUSE,
    STAGE,

    // --- nodes: fn ---
    FN_DEF,
    FN_PARAM_LIST,
    FN_PARAM,
    INTRINSIC_BODY,
    PARTIAL_MODIFIER,      // `partial` before a helper `let` — opts out of the totality check
    PRIVATE_MODIFIER,      // `private` before a `let` — keeps it out of the published surface

    // --- nodes: example ---
    EXAMPLE_DEF,            // example <target> | row | row ...
    EXAMPLE_ROW,            // [ "desc" : ] ( args ) [with binding, ...] -> expected
    EXAMPLES_FILE_HEADER,   // examples for <module.path>   (attached example file)
    WITH_CLAUSE,            // with <dep> = <expr> (, <dep> = <expr>)*
    WITH_BINDING,           // <dep> = <expr>

    // --- nodes: fake ---
    FAKE_DEF,              // fake <injected> | row | row ...
    FAKE_ROW,             // ( args ) -> output   |   _ -> output (a default)

    // --- nodes: types ---
    RET_TYPE,
    TYPE_REF,
    TYPE_ARGS,
    TUPLE_TYPE,
    FN_TYPE,

    // --- nodes: statements inside a behavior body / block ---
    LET_STMT,
    LET_DESTRUCTURE,    // let <pattern> = e
    GUARD_STMT,

    // --- nodes: binding patterns (a `let` statement, a helper or lambda parameter) ---
    PATTERN_NAME,       // x
    PATTERN_TUPLE,      // ( p, p, ... )
    PATTERN_CTOR,       // Name( p )  — a newtype opened by its constructor
    PATTERN_RECORD,     // { f, f = x }
    PATTERN_FIELD,      // f  or  f = x

    // --- nodes: expressions ---
    BLOCK_EXPR,         // { stmts result } and the bare-brace block form
    PIPE_EXPR,          // a |> b
    BINARY_EXPR,        // a <op> b (all precedence levels)
    UNARY_EXPR,         // -a
    APPLY_EXPR,         // <expr>(args) — what is applied is any expression
    ARG_LIST,
    FIELD_ACCESS,       // a.b
    VAR_EXPR,           // a bare identifier
    LITERAL_EXPR,       // int / decimal / string / true / false
    PAREN_EXPR,         // ( e )
    TUPLE_EXPR,         // ( e1, e2, ... )
    LIST_EXPR,          // [ e, ... ]
    LIST_COMP,          // [ e | guard, ... ]
    IF_EXPR,
    ELSE_ARMS,          // else | clause -> e | clause -> e ...  (an attempt's per-clause departures)
    ELSE_ARM,           // | <clause name> -> e   and   | _ -> e
    MATCH_EXPR,
    MATCH_CASE,
    LAMBDA_EXPR,        // x -> e  and  (a, b) -> e
    FIELD_GETTER,       // .field  = the getter (x) -> x.field
    NEW_DATA_EXPR,      // TypeName { field = e, ... }
    FIELD_INIT,
    UNREACHABLE_EXPR;   // unreachable "reason"

    /** Whitespace and comments: kept in the tree, invisible to the parser's token cursor. */
    public boolean isTrivia() {
        return this == WHITESPACE || this == LINE_COMMENT;
    }

    /** A reader-facing name for an "expected X but found Y" message. A literal symbol or keyword is
     * locale-neutral and returned as a backtick string ({@code `:`}); a category (a name, a literal,
     * end of input) is language-dependent and returned as a {@link Localizable}, localized when the
     * message is rendered. Mirrors the older {@code TokenType.display()}. */
    public Object display() {
        return switch (this) {
            case IDENT -> Localizable.of("tok.name");
            case INT_LIT -> Localizable.of("tok.integer");
            case DECIMAL_LIT -> Localizable.of("tok.decimal");
            case STRING_LIT -> Localizable.of("tok.string");
            case TYPEVAR -> Localizable.of("tok.typevar");
            case EOF -> Localizable.of("tok.eof");
            case LBRACE -> "`{`";
            case RBRACE -> "`}`";
            case LPAREN -> "`(`";
            case RPAREN -> "`)`";
            case LBRACKET -> "`[`";
            case RBRACKET -> "`]`";
            case COLON -> "`:`";
            case COMMA -> "`,`";
            case DOT -> "`.`";
            case SPREAD -> "`...`";
            case ASSIGN -> "`=`";
            case PIPE -> "`|`";
            case ARROW -> "`->`";
            case LARROW -> "`<-`";
            case PIPEFWD -> "`>->`";
            case VPIPE -> "`|>`";
            case QUESTION -> "`?`";
            case PLUSPLUS -> "`++`";
            case EQ -> "`==`";
            case NE -> "`/=`";
            case LT -> "`<`";
            case LE -> "`<=`";
            case GT -> "`>`";
            case GE -> "`>=`";
            case AND -> "`&&`";
            case OR -> "`||`";
            case PLUS -> "`+`";
            case MINUS -> "`-`";
            case STAR -> "`*`";
            case SLASH -> "`/`";
            case MODULE_KW -> "`module`";
            case IMPORT_KW -> "`import`";
            case EXPOSING_KW -> "`exposing`";
            case DATA_KW -> "`data`";
            case INVARIANT_KW -> "`invariant`";
            case AS_KW -> "`as`";
            case LET_KW -> "`let`";
            case GUARD_KW -> "`guard`";
            case ELSE_KW -> "`else`";
            case TRUE_KW -> "`true`";
            case FALSE_KW -> "`false`";
            case IF_KW -> "`if`";
            case THEN_KW -> "`then`";
            case BEHAVIOR_KW -> "`behavior`";
            case DEPENDS_KW -> "`depends`";
            case CONSTRUCTS_KW -> "`constructs`";
            case MATCH_KW -> "`match`";
            case WITH_KW -> "`with`";
            case UNREACHABLE_KW -> "`unreachable`";
            default -> "`" + name().toLowerCase(Locale.ROOT) + "`";
        };
    }
}
