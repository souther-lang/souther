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
 * nothing else. For all but ten pairs of kinds the pair alone decides; those ten are held with
 * each construct's answer, and a construct whose answer is not a fact about the kinds at all holds
 * a face below. A pair no list holds is refused rather than given a default, because a
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
        Pair pair = new Pair(asWritten(left), asWritten(right));
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
        String face = faceFor(FACES, joining, pair.left(), pair.right());
        if (face != null) {
            return face;
        }
        throw new IllegalStateException(
                "no rule for " + left + " " + right + " (under " + joining + ")"
                        + "; a new adjacency is a decision and it is made in Spacing");
    }

    /**
     * What the pair alone says, wherever it occurs, or null where no such row holds it. Read by
     * {@code TheRuleAnswersEveryBoundaryTheGrammarCanBuildTest} to hold it against the answer below
     * it: a row read before a construct's face is a row that has to agree with every face it
     * outranks, and it is the only way to see where it does not.
     */
    static String pairAnswer(SyntaxKind left, SyntaxKind right) {
        Pair pair = new Pair(asWritten(left), asWritten(right));
        if (TIGHT_PAIRS.contains(pair)) {
            return TIGHT;
        }
        return SPACED_PAIRS.contains(pair) ? SPACED : null;
    }

    /** What {@code joining}'s own faces say about this pair, or null where none of them covers it. */
    static String faceAnswer(SyntaxKind joining, SyntaxKind left, SyntaxKind right) {
        return faceFor(FACES, joining, asWritten(left), asWritten(right));
    }

    private record Pair(SyntaxKind left, SyntaxKind right) {
    }

    /**
     * One side of a construct, and what it writes against whatever stands on the other. A null side
     * is the whatever.
     */
    private record Face(SyntaxKind construct, SyntaxKind left, SyntaxKind right) {
    }

    /**
     * The kinds that are one value written out. They are one class for this question and the rows
     * are read under one of them, which is what makes the rule answer for a decimal where a source
     * wrote an integer, or for a string where it wrote a name — the kinds a corpus reaches one of
     * and a source reaches another.
     *
     * <p>This is a compression of the rows and not a second input to the rule: the rows are still
     * written between two token kinds, and {@link #decided()} refuses to load if two of them
     * disagree once read this way. Nothing outside here reads the class, and the specification's
     * own transcription of the rule is written kind by kind, so it is not this claim that is being
     * checked against the canonical form — it is the answers.
     */
    private static final Set<SyntaxKind> WRITTEN_VALUES = Set.of(SyntaxKind.INT_LIT,
            SyntaxKind.DECIMAL_LIT, SyntaxKind.STRING_LIT, SyntaxKind.TRUE_KW, SyntaxKind.FALSE_KW);

    private static SyntaxKind asWritten(SyntaxKind kind) {
        return WRITTEN_VALUES.contains(kind) ? SyntaxKind.INT_LIT : kind;
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
            IDENT COLON    LET_STMT         tight
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
            MINUS LPAREN   UNARY_EXPR       tight
            MINUS LPAREN   BINARY_EXPR      spaced
            LT LPAREN      TYPE_ARGS        tight
            LT LPAREN      BINARY_EXPR      spaced
            MINUS IDENT    UNARY_EXPR       tight
            MINUS IDENT    BINARY_EXPR      spaced
            MINUS INT_LIT  UNARY_EXPR       tight
            MINUS INT_LIT  BINARY_EXPR      spaced
            """;

    /**
     * The pairs written with nothing between them wherever they occur. Transcribed rather than
     * grouped, because it does not compress: sorting the kinds into words, brackets, commas, dots
     * and operators leaves eight of the eighteen class pairs the rows reach taking both answers —
     * {@code ):} against {@code ) ->}, {@code <'a} against {@code + 1}, {@code 1)} against
     * {@code then [} — so the pair is the smaller statement.
     */
    private static final String TIGHT_ROWS = """
            DECIMAL_LIT COMMA
            DECIMAL_LIT RPAREN
            DOT IDENT
            FALSE_KW COMMA
            GT COMMA
            GT GT
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
            LBRACKET LPAREN
            LBRACKET RBRACKET
            LBRACKET STRING_LIT
            LPAREN DECIMAL_LIT
            LPAREN DOT
            LPAREN IF_KW
            LPAREN INT_LIT
            LPAREN LBRACE
            LPAREN LBRACKET
            LPAREN LPAREN
            LPAREN MINUS
            LPAREN RPAREN
            LPAREN STRING_LIT
            LPAREN TYPEVAR
            LT TYPEVAR
            QUESTION COMMA
            RBRACE COMMA
            RBRACE RBRACKET
            RBRACE RPAREN
            RBRACKET COMMA
            RBRACKET RPAREN
            RPAREN COLON
            RPAREN COMMA
            RPAREN DOT
            RPAREN LPAREN
            RPAREN RBRACKET
            SPREAD IDENT
            STRING_LIT COMMA
            STRING_LIT RBRACKET
            STRING_LIT RPAREN
            TRUE_KW COMMA
            TRUE_KW RPAREN
            TYPEVAR COMMA
            TYPEVAR GT
            TYPEVAR QUESTION
            """;

    /** The pairs written with one space between them wherever they occur. */
    private static final String SPACED_ROWS = """
            AND IDENT
            ARROW FALSE_KW
            ARROW IDENT
            ARROW IF_KW
            ARROW INT_LIT
            ARROW LBRACE
            ARROW LBRACKET
            ARROW LPAREN
            ARROW MATCH_KW
            ARROW TRUE_KW
            ARROW TYPEVAR
            ARROW UNREACHABLE_KW
            ASSIGN DOT
            ASSIGN FALSE_KW
            ASSIGN IDENT
            ASSIGN IF_KW
            ASSIGN INT_LIT
            ASSIGN LBRACE
            ASSIGN LBRACKET
            ASSIGN LPAREN
            ASSIGN MATCH_KW
            ASSIGN MINUS
            ASSIGN STRING_LIT
            ASSIGN TRUE_KW
            AS_KW IDENT
            BEHAVIOR_KW IDENT
            COLON IDENT
            COLON LPAREN
            COLON TYPEVAR
            COMMA DECIMAL_LIT
            COMMA FALSE_KW
            COMMA IDENT
            COMMA INT_LIT
            COMMA LBRACKET
            COMMA LPAREN
            COMMA MATCH_KW
            COMMA STRING_LIT
            COMMA TRUE_KW
            COMMA TYPEVAR
            CONSTRUCTS_KW IDENT
            DATA_KW IDENT
            DECIMAL_LIT AND
            DECIMAL_LIT MINUS
            DECIMAL_LIT THEN_KW
            DEPENDS_KW IDENT
            ELSE_KW IDENT
            ELSE_KW IF_KW
            ELSE_KW INT_LIT
            ELSE_KW LBRACKET
            ELSE_KW LPAREN
            ELSE_KW TRUE_KW
            EQ IDENT
            EQ INT_LIT
            EXPOSING_KW LPAREN
            FALSE_KW ELSE_KW
            FALSE_KW RBRACE
            GE DECIMAL_LIT
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
            IDENT LE
            IDENT LET_KW
            IDENT MINUS
            IDENT OR
            IDENT PIPE
            IDENT PIPEFWD
            IDENT PLUS
            IDENT PLUSPLUS
            IDENT RBRACE
            IDENT STAR
            IDENT STRING_LIT
            IDENT THEN_KW
            IDENT VPIPE
            IDENT WITH_KW
            IF_KW IDENT
            IMPORT_KW IDENT
            INT_LIT AND
            INT_LIT ARROW
            INT_LIT ELSE_KW
            INT_LIT MINUS
            INT_LIT PLUS
            INT_LIT RBRACE
            INT_LIT SLASH
            INT_LIT THEN_KW
            INT_LIT VPIPE
            INVARIANT_KW IDENT
            LBRACE IDENT
            LBRACE SPREAD
            LE DECIMAL_LIT
            LE INT_LIT
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
            PLUS IDENT
            PLUS INT_LIT
            PLUS LPAREN
            PLUSPLUS IDENT
            PLUSPLUS LBRACKET
            RBRACE ARROW
            RBRACE ASSIGN
            RBRACE AS_KW
            RBRACE ELSE_KW
            RBRACE RBRACE
            RBRACKET ELSE_KW
            RBRACKET RBRACE
            RPAREN AND
            RPAREN ARROW
            RPAREN ASSIGN
            RPAREN AS_KW
            RPAREN ELSE_KW
            RPAREN EQ
            RPAREN GE
            RPAREN LE
            RPAREN LT
            RPAREN PLUS
            RPAREN PLUSPLUS
            RPAREN RBRACE
            RPAREN STAR
            RPAREN THEN_KW
            RPAREN VPIPE
            RPAREN WITH_KW
            SLASH IDENT
            STAR DECIMAL_LIT
            STAR IDENT
            STAR INT_LIT
            STAR LPAREN
            STRING_LIT ARROW
            STRING_LIT COLON
            STRING_LIT PLUSPLUS
            STRING_LIT RBRACE
            THEN_KW DECIMAL_LIT
            THEN_KW FALSE_KW
            THEN_KW IDENT
            THEN_KW INT_LIT
            THEN_KW LBRACKET
            THEN_KW LPAREN
            TRUE_KW RBRACE
            TYPEVAR ASSIGN
            UNREACHABLE_KW STRING_LIT
            VPIPE IDENT
            WITH_KW IDENT
            """;


    /**
     * What a construct writes at one of its own sides, whatever stands on the other. A {@code *} is
     * that whatever.
     *
     * <p>These are the constructs whose answer is not a fact about the two kinds. What a field read
     * writes around its dot is the same whether the value before it is a name, a call or a record
     * literal — there is no pair of kinds to consult, because the left side is whatever an
     * expression can end with, and that is not a list this rule should be keeping. Written pair by
     * pair the rows would be the product of the kinds and would still be short of the next kind an
     * expression learns to end with.
     *
     * <p>Read after the pairs, so a pair the corpus reached says what it says and these answer only
     * where it did not. The narrowest face that covers a boundary wins, which is how a construct
     * written open still writes its empty brackets tight. That the two together answer every
     * boundary the grammar can build is what
     * {@code TheRuleAnswersEveryBoundaryTheGrammarCanBuildTest} says.
     */
    private static final String FACE_ROWS = """
            # A name written through what holds it is one name.
            QUALIFIED_NAME  *       DOT     tight
            QUALIFIED_NAME  DOT     *       tight
            FIELD_ACCESS    *       DOT     tight
            FIELD_ACCESS    DOT     *       tight
            FIELD_GETTER    DOT     *       tight
            SPREAD_MEMBER   SPREAD  *       tight
            SPREAD_MEMBER   *       DOT     tight
            SPREAD_MEMBER   DOT     *       tight
            STAGE           *       DOT     tight
            STAGE           DOT     *       tight
            CONSTRUCTS_CLAUSE  *    DOT     tight
            CONSTRUCTS_CLAUSE  DOT  *       tight
            DEPENDS_CLAUSE  *       DOT     tight
            DEPENDS_CLAUSE  DOT     *       tight
            # What is applied, opened or negated is written against it.
            APPLY_EXPR      *       LPAREN  tight
            UNARY_EXPR      MINUS   *       tight
            PAREN_EXPR      LPAREN  *       tight
            PAREN_EXPR      *       RPAREN  tight
            # An operator is spaced from both of its operands.
            BINARY_EXPR     *       *       spaced
            PIPE_EXPR       *       *       spaced
            # A bracketed construct written tight, and its commas.
            ARG_LIST        LPAREN  *       tight
            ARG_LIST        *       RPAREN  tight
            ARG_LIST        *       COMMA   tight
            ARG_LIST        COMMA   *       spaced
            LIST_EXPR       LBRACKET *      tight
            LIST_EXPR       *       RBRACKET tight
            LIST_EXPR       *       COMMA   tight
            LIST_EXPR       COMMA   *       spaced
            TUPLE_EXPR      LPAREN  *       tight
            TUPLE_EXPR      *       RPAREN  tight
            TUPLE_EXPR      *       COMMA   tight
            TUPLE_EXPR      COMMA   *       spaced
            TUPLE_TYPE      LPAREN  *       tight
            TUPLE_TYPE      *       RPAREN  tight
            TUPLE_TYPE      *       COMMA   tight
            TUPLE_TYPE      COMMA   *       spaced
            TYPE_ARGS       LT      *       tight
            TYPE_ARGS       *       GT      tight
            TYPE_ARGS       *       COMMA   tight
            TYPE_ARGS       COMMA   *       spaced
            PARAM_LIST      LPAREN  *       tight
            PARAM_LIST      *       RPAREN  tight
            PARAM_LIST      *       COMMA   tight
            PARAM_LIST      COMMA   *       spaced
            FN_PARAM_LIST   LPAREN  *       tight
            FN_PARAM_LIST   *       RPAREN  tight
            FN_PARAM_LIST   *       COMMA   tight
            FN_PARAM_LIST   COMMA   *       spaced
            FN_TYPE         LPAREN  *       tight
            FN_TYPE         *       RPAREN  tight
            FN_TYPE         *       COMMA   tight
            FN_TYPE         COMMA   *       spaced
            FN_TYPE         *       ARROW   spaced
            FN_TYPE         ARROW   *       spaced
            LAMBDA_EXPR     LPAREN  *       tight
            LAMBDA_EXPR     *       RPAREN  tight
            LAMBDA_EXPR     *       COMMA   tight
            LAMBDA_EXPR     COMMA   *       spaced
            LAMBDA_EXPR     *       ARROW   spaced
            LAMBDA_EXPR     ARROW   *       spaced
            PATTERN_TUPLE   LPAREN  *       tight
            PATTERN_TUPLE   *       RPAREN  tight
            PATTERN_TUPLE   *       COMMA   tight
            PATTERN_TUPLE   COMMA   *       spaced
            PATTERN_CTOR    LPAREN  *       tight
            PATTERN_CTOR    *       RPAREN  tight
            LIST_COMP       LBRACKET *      tight
            LIST_COMP       *       RBRACKET tight
            LIST_COMP       *       COMMA   tight
            LIST_COMP       COMMA   *       spaced
            LIST_COMP       *       PIPE    spaced
            LIST_COMP       PIPE    *       spaced
            # A bracketed construct written open.
            EXPOSING_CLAUSE LPAREN  RPAREN  tight
            EXPOSING_CLAUSE LPAREN  *       spaced
            EXPOSING_CLAUSE *       RPAREN  spaced
            EXPOSING_CLAUSE *       COMMA   tight
            EXPOSING_CLAUSE COMMA   *       spaced
            NAME_LIST       LPAREN  RPAREN  tight
            NAME_LIST       LPAREN  *       spaced
            NAME_LIST       *       RPAREN  spaced
            NAME_LIST       *       COMMA   tight
            NAME_LIST       COMMA   *       spaced
            NEW_DATA_EXPR   LBRACE  RBRACE  tight
            NEW_DATA_EXPR   LBRACE  *       spaced
            NEW_DATA_EXPR   *       RBRACE  spaced
            NEW_DATA_EXPR   *       COMMA   tight
            NEW_DATA_EXPR   COMMA   *       spaced
            PATTERN_RECORD  LBRACE  RBRACE  tight
            PATTERN_RECORD  LBRACE  *       spaced
            PATTERN_RECORD  *       RBRACE  spaced
            PATTERN_RECORD  *       COMMA   tight
            PATTERN_RECORD  COMMA   *       spaced
            PATTERN_RECORD  *       ASSIGN  spaced
            PATTERN_RECORD  ASSIGN  *       spaced
            PRODUCT_BODY    LBRACE  RBRACE  tight
            PRODUCT_BODY    LBRACE  *       spaced
            PRODUCT_BODY    COMMA   *       spaced
            # What a declaration writes around its own words.
            DATA_DEF        DATA_KW *       spaced
            DATA_DEF        *       ASSIGN  spaced
            DATA_DEF        ASSIGN  *       spaced
            FN_DEF          LET_KW  *       spaced
            FN_DEF          *       COLON   tight
            FN_DEF          COLON   *       spaced
            FN_DEF          *       ASSIGN  spaced
            FN_DEF          ASSIGN  *       spaced
            LET_STMT        LET_KW  *       spaced
            LET_STMT        *       COLON   tight
            LET_STMT        COLON   *       spaced
            LET_STMT        *       ASSIGN  spaced
            LET_STMT        ASSIGN  *       spaced
            LET_DESTRUCTURE LET_KW  *       spaced
            LET_DESTRUCTURE *       ASSIGN  spaced
            LET_DESTRUCTURE ASSIGN  *       spaced
            GUARD_STMT      GUARD_KW *      spaced
            GUARD_STMT      *       ELSE_KW spaced
            GUARD_STMT      ELSE_KW *       spaced
            GUARD_STMT      *       AS_KW   spaced
            GUARD_STMT      AS_KW   *       spaced
            IF_EXPR         IF_KW   *       spaced
            IF_EXPR         *       THEN_KW spaced
            IF_EXPR         THEN_KW *       spaced
            IF_EXPR         *       ELSE_KW spaced
            IF_EXPR         ELSE_KW *       spaced
            IF_EXPR         *       AS_KW   spaced
            IF_EXPR         AS_KW   *       spaced
            MATCH_EXPR      MATCH_KW *      spaced
            MATCH_EXPR      *       WITH_KW spaced
            MATCH_CASE      LPAREN  RPAREN  tight
            MATCH_CASE      LBRACE  RBRACE  tight
            MATCH_CASE      *       DOT     tight
            MATCH_CASE      DOT     *       tight
            MATCH_CASE      *       LPAREN  tight
            MATCH_CASE      LPAREN  *       tight
            MATCH_CASE      *       RPAREN  tight
            MATCH_CASE      *       COMMA   tight
            MATCH_CASE      COMMA   *       spaced
            MATCH_CASE      *       LBRACE  spaced
            MATCH_CASE      LBRACE  *       spaced
            MATCH_CASE      *       RBRACE  spaced
            MATCH_CASE      *       PIPE    spaced
            MATCH_CASE      PIPE    *       spaced
            MATCH_CASE      *       AS_KW   spaced
            MATCH_CASE      AS_KW   *       spaced
            MATCH_CASE      *       ASSIGN  spaced
            MATCH_CASE      ASSIGN  *       spaced
            MATCH_CASE      RBRACE  IDENT   spaced
            MATCH_CASE      RPAREN  IDENT   spaced
            MATCH_CASE      *       ARROW   spaced
            MATCH_CASE      ARROW   *       spaced
            ELSE_ARM        PIPE    *       spaced
            ELSE_ARM        *       ARROW   spaced
            ELSE_ARM        ARROW   *       spaced
            UNREACHABLE_EXPR UNREACHABLE_KW * spaced
            FIELD_INIT      *       ASSIGN  spaced
            FIELD_INIT      ASSIGN  *       spaced
            WITH_BINDING    *       ASSIGN  spaced
            WITH_BINDING    ASSIGN  *       spaced
            FIELD           *       COLON   tight
            FIELD           COLON   *       spaced
            FIELD           *       QUESTION tight
            PARAM           *       COLON   tight
            PARAM           COLON   *       spaced
            FN_PARAM        *       COLON   tight
            FN_PARAM        COLON   *       spaced
            EXPOSED_ENTRY   *       COLON   spaced
            EXPOSED_ENTRY   COLON   *       spaced
            RET_TYPE        *       PIPE    spaced
            RET_TYPE        PIPE    *       spaced
            RET_TYPE        *       QUESTION tight
            SUM_BODY        *       PIPE    spaced
            SUM_BODY        PIPE    *       spaced
            INVARIANT_CLAUSE INVARIANT_KW * spaced
            INVARIANT_CLAUSE *      ASSIGN  spaced
            INVARIANT_CLAUSE ASSIGN *       spaced
            EXAMPLE_ROW     *       COLON   spaced
            EXAMPLE_ROW     COLON   *       spaced
            EXAMPLE_ROW     *       ARROW   spaced
            EXAMPLE_ROW     ARROW   *       spaced
            EXAMPLE_ROW     *       WITH_KW spaced
            FAKE_ROW        *       ARROW   spaced
            FAKE_ROW        ARROW   *       spaced
            EXAMPLE_DEF     PIPE    *       spaced
            FAKE_DEF        PIPE    *       spaced
            MATCH_EXPR      PIPE    *       spaced
            BEHAVIOR_SIG    *       ARROW   spaced
            BEHAVIOR_SIG    ARROW   *       spaced
            PIPE_BEHAVIOR   *       PIPEFWD spaced
            PIPE_BEHAVIOR   PIPEFWD *       spaced
            PIPE_BEHAVIOR   *       ARROW   spaced
            PIPE_BEHAVIOR   ARROW   *       spaced
            """;

    private static Map<Face, String> faces() {
        Map<Face, String> out = new HashMap<>();
        for (String line : FACE_ROWS.split("\n")) {
            if (line.isBlank() || line.strip().startsWith("#")) {
                continue;
            }
            String[] parts = line.strip().split("\\s+");
            SyntaxKind construct = SyntaxKind.valueOf(parts[0]);
            SyntaxKind left = parts[1].equals("*") ? null : asWritten(SyntaxKind.valueOf(parts[1]));
            SyntaxKind right = parts[2].equals("*") ? null : asWritten(SyntaxKind.valueOf(parts[2]));
            out.put(new Face(construct, left, right), parts[3].equals("spaced") ? SPACED : TIGHT);
        }
        return out;
    }


    /** What {@code construct}'s faces say about this pair: the narrowest that covers it, so that a
     * construct written open can still write its empty brackets tight. */
    private static String faceFor(Map<Face, String> faces, SyntaxKind construct, SyntaxKind left,
            SyntaxKind right) {
        String exact = faces.get(new Face(construct, left, right));
        if (exact != null) {
            return exact;
        }
        String byLeft = faces.get(new Face(construct, left, null));
        if (byLeft != null) {
            return byLeft;
        }
        String byRight = faces.get(new Face(construct, null, right));
        return byRight != null ? byRight : faces.get(new Face(construct, null, null));
    }

    private static final Set<Pair> TIGHT_PAIRS = pairs(TIGHT_ROWS);
    private static final Set<Pair> SPACED_PAIRS = disjointFrom(TIGHT_PAIRS, pairs(SPACED_ROWS));

    /** The two lists read under the class above, and refused if a pair lands in both. */
    private static Set<Pair> disjointFrom(Set<Pair> tight, Set<Pair> spaced) {
        for (Pair p : spaced) {
            if (tight.contains(p)) {
                throw new IllegalStateException(
                        "two rows for " + p.left() + " " + p.right() + " disagree");
            }
        }
        return spaced;
    }
    private static final Map<Pair, Map<SyntaxKind, String>> DECIDED = decided();
    private static final Map<Face, String> FACES = faces();

    private static Set<Pair> pairs(String rows) {
        Set<Pair> out = new HashSet<>();
        for (String line : rows.split("\n")) {
            if (line.isBlank() || line.startsWith("#")) {
                continue;
            }
            String[] parts = line.strip().split("\\s+");
            out.add(new Pair(asWritten(SyntaxKind.valueOf(parts[0])),
                    asWritten(SyntaxKind.valueOf(parts[1]))));
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
            Pair pair = new Pair(asWritten(SyntaxKind.valueOf(parts[0])),
                    asWritten(SyntaxKind.valueOf(parts[1])));
            String answer = parts[3].equals("spaced") ? SPACED : TIGHT;
            String before = out.computeIfAbsent(pair, _ -> new EnumMap<>(SyntaxKind.class))
                    .put(SyntaxKind.valueOf(parts[2]), answer);
            if (before != null && !before.equals(answer)) {
                throw new IllegalStateException("two rows for " + line.strip() + " disagree");
            }
        }
        return out;
    }
}
