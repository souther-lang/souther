package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the canonical form writes between two code tokens that share a line. There is no third
 * answer: nothing, or one space.
 *
 * <p>Which of the two is read from the kind on each side and the construct joining them, and from
 * nothing else. For all but nine pairs of kinds the pair alone decides; those nine are held with
 * each construct's answer. A pair no list holds is refused rather than given a default, because a
 * new adjacency is a decision and this is where it is made — the alternative is that it is made by
 * whichever construct happens to write it first, which is the arrangement issue #476 describes.
 *
 * <p><b>Which construct.</b> The joining construct is the one the <em>canonical form</em> writes,
 * not the node the source had. The two differ wherever the formatter rewrites what it read:
 * {@code let f = (x) -> x} is written {@code let f (x) = x}, so those parentheses come from a
 * lambda in the source and are a parameter list in the output, and it is the output's name that
 * belongs here. A caller marking its documents with the source's name would be asking this function
 * a question about a construct its reader cannot look up.
 *
 * <p>The rows were read from the canonical form over a corpus that builds every kind of node the
 * grammar has, and {@code TheSpacingRuleAgreesWithTheCanonicalFormTest} holds them against it. That
 * test measures the rendered text; it is not given this table to measure against.
 */
final class Spacing {

    /** Written with nothing between them. */
    static final String TIGHT = "";

    /** Written with one space between them. */
    static final String SPACED = " ";

    private Spacing() {
    }

    /**
     * What goes between a {@code left} and a {@code right} token that {@code joining} holds on one
     * line. Not asked of two tokens a break separates: what is written there is the break rules'
     * and this function has no answer for it.
     */
    static String between(SyntaxKind joining, SyntaxKind left, SyntaxKind right) {
        Pair pair = new Pair(left, right);
        Map<SyntaxKind, String> byConstruct = DECIDED.get(pair);
        if (byConstruct != null) {
            String answer = byConstruct.get(joining);
            if (answer == null) {
                throw new IllegalStateException(
                        "no rule for " + left + " " + right + " under " + joining
                                + "; this pair is written both ways and the constructs that join it"
                                + " are listed in Spacing");
            }
            return answer;
        }
        if (TIGHT_PAIRS.contains(pair)) {
            return TIGHT;
        }
        if (SPACED_PAIRS.contains(pair)) {
            return SPACED;
        }
        throw new IllegalStateException(
                "no rule for " + left + " " + right + " (under " + joining + ")"
                        + "; a new adjacency is a decision and it is made in Spacing");
    }

    private record Pair(SyntaxKind left, SyntaxKind right) {
    }

    /**
     * The pairs the joining construct decides, and what each construct answers. These are the pairs
     * written both ways somewhere in the corpus; every other pair takes one answer wherever it
     * occurs.
     */
    private static final String DECIDED_ROWS = """
            # A list of names is written open — `exposing ( a, b )`, `import m ( a, b )` — and every
            # other bracketed construct is not.
            LPAREN IDENT   EXPOSING_CLAUSE  spaced
            LPAREN IDENT   NAME_LIST        spaced
            LPAREN IDENT   ARG_LIST         tight
            LPAREN IDENT   PARAM_LIST       tight
            LPAREN IDENT   FN_PARAM_LIST    tight
            LPAREN IDENT   FN_TYPE          tight
            LPAREN IDENT   LAMBDA_EXPR      tight
            LPAREN IDENT   MATCH_CASE       tight
            LPAREN IDENT   PAREN_EXPR       tight
            LPAREN IDENT   PATTERN_CTOR     tight
            LPAREN IDENT   PATTERN_TUPLE    tight
            LPAREN IDENT   TUPLE_EXPR       tight
            LPAREN IDENT   TUPLE_TYPE       tight
            IDENT RPAREN   EXPOSING_CLAUSE  spaced
            IDENT RPAREN   NAME_LIST        spaced
            IDENT RPAREN   ARG_LIST         tight
            IDENT RPAREN   PARAM_LIST       tight
            IDENT RPAREN   FN_PARAM_LIST    tight
            IDENT RPAREN   FN_TYPE          tight
            IDENT RPAREN   LAMBDA_EXPR      tight
            IDENT RPAREN   MATCH_CASE       tight
            IDENT RPAREN   PAREN_EXPR       tight
            IDENT RPAREN   PATTERN_CTOR     tight
            IDENT RPAREN   PATTERN_TUPLE    tight
            IDENT RPAREN   TUPLE_EXPR       tight
            IDENT RPAREN   TUPLE_TYPE       tight
            # A declaration's name is spaced from what follows it; what is applied or opened is not.
            IDENT LPAREN   FN_DEF           spaced
            IDENT LPAREN   IMPORT_DECL      spaced
            IDENT LPAREN   APPLY_EXPR       tight
            IDENT LPAREN   MATCH_CASE       tight
            IDENT LPAREN   PATTERN_CTOR     tight
            # A type ascribed to a name is written tight against it; a signature is spaced from its
            # name.
            IDENT COLON    BEHAVIOR_DEF     spaced
            IDENT COLON    EXPOSED_ENTRY    spaced
            IDENT COLON    FIELD            tight
            IDENT COLON    FN_DEF           tight
            IDENT COLON    FN_PARAM         tight
            IDENT COLON    PARAM            tight
            # `<` and `>` are a type's brackets or a comparison's operator.
            IDENT LT       TYPE_REF         tight
            IDENT LT       BINARY_EXPR      spaced
            LT IDENT       TYPE_ARGS        tight
            LT IDENT       BINARY_EXPR      spaced
            IDENT GT       TYPE_ARGS        tight
            IDENT GT       BINARY_EXPR      spaced
            RPAREN GT      TYPE_ARGS        tight
            RPAREN GT      BINARY_EXPR      spaced
            # `-` negates or subtracts.
            MINUS IDENT    UNARY_EXPR       tight
            MINUS IDENT    BINARY_EXPR      spaced
            """;

    /**
     * The pairs written with nothing between them wherever they occur. Transcribed rather than
     * grouped, because it does not compress: sorting the kinds into words, brackets, commas, dots
     * and operators leaves eight of the twenty-four class pairs taking both answers — {@code ):}
     * against {@code ) ->}, {@code -n} against {@code + 1}, {@code Amount(} against {@code P (} —
     * so the pair is the smaller statement.
     */
    private static final String TIGHT_ROWS = """
            DECIMAL_LIT COMMA
            DOT IDENT
            FALSE_KW COMMA
            GT COMMA
            GT GT
            GT RPAREN
            IDENT COMMA
            IDENT DOT
            IDENT QUESTION
            IDENT RBRACKET
            INT_LIT COMMA
            INT_LIT RBRACKET
            INT_LIT RPAREN
            LBRACE RBRACE
            LBRACKET IDENT
            LBRACKET INT_LIT
            LBRACKET STRING_LIT
            LBRACKET LPAREN
            LBRACKET RBRACKET
            LPAREN INT_LIT
            LPAREN DECIMAL_LIT
            DECIMAL_LIT RPAREN
            LPAREN DOT
            LPAREN MINUS
            LPAREN LBRACE
            LPAREN LBRACKET
            LPAREN LPAREN
            LPAREN RPAREN
            LPAREN STRING_LIT
            LPAREN TYPEVAR
            LT LPAREN
            LT TYPEVAR
            MINUS LPAREN
            QUESTION COMMA
            QUESTION RPAREN
            RBRACE COMMA
            RBRACE RBRACKET
            RBRACE RPAREN
            RBRACKET COMMA
            RBRACKET RPAREN
            RPAREN COLON
            RPAREN COMMA
            RPAREN RBRACKET
            RPAREN RPAREN
            SPREAD IDENT
            STRING_LIT RPAREN
            STRING_LIT COMMA
            STRING_LIT RBRACKET
            TRUE_KW RPAREN
            TRUE_KW COMMA
            TYPEVAR COMMA
            TYPEVAR GT
            TYPEVAR QUESTION
            TYPEVAR RPAREN
            """;

    /** The pairs written with one space between them wherever they occur. */
    private static final String SPACED_ROWS = """
            AND IDENT
            ARROW IDENT
            ARROW IF_KW
            ARROW INT_LIT
            ARROW LBRACE
            ARROW LBRACKET
            ARROW LPAREN
            ARROW MATCH_KW
            ARROW TYPEVAR
            ARROW UNREACHABLE_KW
            ASSIGN DOT
            ASSIGN IDENT
            ASSIGN IF_KW
            ASSIGN INT_LIT
            ASSIGN LBRACE
            ASSIGN LBRACKET
            ASSIGN LPAREN
            ASSIGN MINUS
            ASSIGN STRING_LIT
            ASSIGN TRUE_KW
            ASSIGN FALSE_KW
            AS_KW IDENT
            BEHAVIOR_KW IDENT
            COLON IDENT
            COLON LPAREN
            COLON TYPEVAR
            COMMA FALSE_KW
            COMMA DECIMAL_LIT
            COMMA IDENT
            COMMA LPAREN
            COMMA MATCH_KW
            COMMA INT_LIT
            COMMA LBRACKET
            COMMA STRING_LIT
            COMMA TRUE_KW
            COMMA TYPEVAR
            CONSTRUCTS_KW IDENT
            DATA_KW IDENT
            DECIMAL_LIT MINUS
            DECIMAL_LIT THEN_KW
            DEPENDS_KW IDENT
            ELSE_KW IDENT
            ELSE_KW IF_KW
            ELSE_KW INT_LIT
            ELSE_KW LPAREN
            ELSE_KW TRUE_KW
            EQ IDENT
            EQ INT_LIT
            EXPOSING_KW LPAREN
            FALSE_KW ELSE_KW
            FALSE_KW RBRACE
            GE IDENT
            GE INT_LIT
            GT ASSIGN
            GT IDENT
            GT INT_LIT
            GUARD_KW IDENT
            IDENT AND
            IDENT ARROW
            IDENT ASSIGN
            IDENT AS_KW
            IDENT ELSE_KW
            IDENT EQ
            IDENT EXPOSING_KW
            IDENT GE
            IDENT IDENT
            IDENT LBRACE
            IDENT LET_KW
            IDENT OR
            IDENT PIPE
            IDENT PIPEFWD
            IDENT PLUS
            IDENT PLUSPLUS
            IDENT RBRACE
            IDENT STRING_LIT
            IDENT THEN_KW
            IDENT VPIPE
            IDENT WITH_KW
            IF_KW IDENT
            IMPORT_KW IDENT
            INT_LIT ELSE_KW
            INT_LIT MINUS
            INT_LIT RBRACE
            INT_LIT THEN_KW
            INVARIANT_KW IDENT
            LBRACE IDENT
            LBRACE SPREAD
            LET_KW IDENT
            LET_KW LBRACE
            LET_KW LPAREN
            LT DECIMAL_LIT
            LT INT_LIT
            MATCH_KW IDENT
            MODULE_KW IDENT
            OR IDENT
            PIPE IDENT
            PIPE LPAREN
            PIPE STRING_LIT
            PIPEFWD IDENT
            PLUS INT_LIT
            PLUSPLUS IDENT
            PLUSPLUS LBRACKET
            RBRACE ARROW
            RBRACE RBRACE
            RBRACE ASSIGN
            RBRACE AS_KW
            RBRACKET ELSE_KW
            RBRACKET RBRACE
            RPAREN ARROW
            RPAREN RBRACE
            RPAREN ASSIGN
            RPAREN AS_KW
            RPAREN ELSE_KW
            RPAREN EQ
            RPAREN STAR
            RPAREN THEN_KW
            RPAREN WITH_KW
            STAR IDENT
            STRING_LIT COLON
            STRING_LIT RBRACE
            THEN_KW DECIMAL_LIT
            TRUE_KW RBRACE
            THEN_KW FALSE_KW
            THEN_KW IDENT
            THEN_KW INT_LIT
            THEN_KW LPAREN
            TYPEVAR ASSIGN
            UNREACHABLE_KW STRING_LIT
            VPIPE IDENT
            WITH_KW IDENT
            """;

    private static final Set<Pair> TIGHT_PAIRS = pairs(TIGHT_ROWS);
    private static final Set<Pair> SPACED_PAIRS = pairs(SPACED_ROWS);
    private static final Map<Pair, Map<SyntaxKind, String>> DECIDED = decided();

    private static Set<Pair> pairs(String rows) {
        Set<Pair> out = new HashSet<>();
        for (String line : rows.split("\n")) {
            if (line.isBlank() || line.startsWith("#")) {
                continue;
            }
            String[] parts = line.strip().split("\\s+");
            out.add(new Pair(SyntaxKind.valueOf(parts[0]), SyntaxKind.valueOf(parts[1])));
        }
        return out;
    }

    private static Map<Pair, Map<SyntaxKind, String>> decided() {
        Map<Pair, Map<SyntaxKind, String>> out = new HashMap<>();
        for (String line : DECIDED_ROWS.split("\n")) {
            if (line.isBlank() || line.strip().startsWith("#")) {
                continue;
            }
            String[] parts = line.strip().split("\\s+");
            Pair pair = new Pair(SyntaxKind.valueOf(parts[0]), SyntaxKind.valueOf(parts[1]));
            out.computeIfAbsent(pair, _ -> new EnumMap<>(SyntaxKind.class))
                    .put(SyntaxKind.valueOf(parts[2]), parts[3].equals("spaced") ? SPACED : TIGHT);
        }
        return out;
    }
}
