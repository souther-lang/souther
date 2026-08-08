package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.cst.SyntaxKind.*;

/**
 * The rule answers every boundary the grammar can build, and not only the ones a corpus happens to
 * write.
 *
 * <p>A corpus that builds every kind of node does not close this. What a construct writes at one of
 * its sides depends on what its child ends with, and a child is an expression — so the left of a
 * field read's dot is whatever an expression can end with, which is nine kinds and not the one the
 * corpus wrote. {@code R { a = x }.a} is an ordinary source and the rule had no row for the brace
 * against the dot; it was the formatter, not the source, that was wrong.
 *
 * <p>So the domain is written out here: for each construct, the token kinds that can stand on each
 * side of each boundary it writes, with the sides that face a child given as what that child can
 * begin and end with. It is an over-approximation on purpose — a pair it holds that the grammar
 * cannot build costs an unused answer, and one it misses costs a source that cannot be formatted.
 * The corpus keeps it honest from below: every boundary the corpus reaches has to be in it.
 */
class TheRuleAnswersEveryBoundaryTheGrammarCanBuildTest {

    private static Set<SyntaxKind> of(SyntaxKind... k) {
        return new LinkedHashSet<>(List.of(k));
    }

    /** What an expression's document can begin and end with, and the same for a type and a
     * pattern. These are the sides of a boundary that face a child rather than a token the
     * construct writes itself. */
    private static final Set<SyntaxKind> EXPR_FIRST = of(IDENT, INT_LIT, DECIMAL_LIT, STRING_LIT,
            TRUE_KW, FALSE_KW, LPAREN, LBRACKET, LBRACE, MINUS, DOT, IF_KW, MATCH_KW, UNREACHABLE_KW);
    private static final Set<SyntaxKind> EXPR_LAST = of(IDENT, INT_LIT, DECIMAL_LIT, STRING_LIT,
            TRUE_KW, FALSE_KW, RPAREN, RBRACKET, RBRACE);
    private static final Set<SyntaxKind> TYPE_FIRST = of(IDENT, TYPEVAR, LPAREN);
    private static final Set<SyntaxKind> TYPE_LAST = of(IDENT, TYPEVAR, RPAREN, GT, QUESTION);
    private static final Set<SyntaxKind> PAT_FIRST = of(IDENT, LPAREN, LBRACE);
    private static final Set<SyntaxKind> PAT_LAST = of(IDENT, RPAREN, RBRACE);
    private static final Set<SyntaxKind> OPS = of(EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS,
            STAR, SLASH, PLUSPLUS);

    private record Face(SyntaxKind construct, Set<SyntaxKind> left, Set<SyntaxKind> right) {}

    private static final List<Face> DOMAIN = List.of(
            new Face(FIELD_ACCESS, EXPR_LAST, of(DOT)),
            new Face(FIELD_ACCESS, of(DOT), of(IDENT)),
            new Face(FIELD_GETTER, of(DOT), of(IDENT)),
            new Face(APPLY_EXPR, EXPR_LAST, of(LPAREN)),
            new Face(PAREN_EXPR, of(LPAREN), EXPR_FIRST),
            new Face(PAREN_EXPR, EXPR_LAST, of(RPAREN)),
            new Face(UNARY_EXPR, of(MINUS), EXPR_FIRST),
            new Face(BINARY_EXPR, EXPR_LAST, OPS),
            new Face(BINARY_EXPR, OPS, EXPR_FIRST),
            new Face(PIPE_EXPR, EXPR_LAST, of(VPIPE)),
            new Face(PIPE_EXPR, of(VPIPE), EXPR_FIRST),
            new Face(ARG_LIST, of(LPAREN), EXPR_FIRST),
            new Face(ARG_LIST, EXPR_LAST, of(RPAREN, COMMA)),
            new Face(ARG_LIST, of(COMMA), EXPR_FIRST),
            new Face(LIST_EXPR, of(LBRACKET), EXPR_FIRST),
            new Face(LIST_EXPR, EXPR_LAST, of(RBRACKET, COMMA)),
            new Face(LIST_EXPR, of(COMMA), EXPR_FIRST),
            new Face(TUPLE_EXPR, of(LPAREN), EXPR_FIRST),
            new Face(TUPLE_EXPR, EXPR_LAST, of(RPAREN, COMMA)),
            new Face(TUPLE_EXPR, of(COMMA), EXPR_FIRST),
            new Face(LIST_COMP, of(LBRACKET), EXPR_FIRST),
            new Face(LIST_COMP, EXPR_LAST, of(PIPE, RBRACKET, COMMA)),
            new Face(LIST_COMP, of(PIPE, COMMA), EXPR_FIRST),
            new Face(NEW_DATA_EXPR, of(IDENT), of(LBRACE)),
            new Face(NEW_DATA_EXPR, of(LBRACE), of(IDENT, SPREAD, RBRACE)),
            new Face(NEW_DATA_EXPR, of(IDENT, RBRACE), of(RBRACE, COMMA)),
            new Face(NEW_DATA_EXPR, EXPR_LAST, of(RBRACE, COMMA)),
            new Face(NEW_DATA_EXPR, of(COMMA), of(IDENT, SPREAD)),
            new Face(FIELD_INIT, of(IDENT), of(ASSIGN)),
            new Face(FIELD_INIT, of(ASSIGN), EXPR_FIRST),
            new Face(IF_EXPR, of(IF_KW), EXPR_FIRST),
            new Face(IF_EXPR, EXPR_LAST, of(THEN_KW, AS_KW)),
            new Face(IF_EXPR, of(THEN_KW, ELSE_KW), EXPR_FIRST),
            new Face(IF_EXPR, EXPR_LAST, of(ELSE_KW)),
            new Face(MATCH_EXPR, of(MATCH_KW), EXPR_FIRST),
            new Face(MATCH_EXPR, EXPR_LAST, of(WITH_KW)),
            new Face(MATCH_CASE, PAT_LAST, of(ARROW)),
            new Face(MATCH_CASE, of(ARROW), EXPR_FIRST),
            new Face(UNREACHABLE_EXPR, of(UNREACHABLE_KW), EXPR_FIRST),
            new Face(LAMBDA_EXPR, PAT_LAST, of(ARROW, RPAREN, COMMA)),
            new Face(LAMBDA_EXPR, of(ARROW), EXPR_FIRST),
            new Face(LAMBDA_EXPR, of(LPAREN, COMMA), PAT_FIRST),
            new Face(LET_STMT, of(LET_KW), of(IDENT)),
            new Face(LET_STMT, of(IDENT, RPAREN, TYPEVAR, GT, QUESTION), of(ASSIGN, COLON)),
            new Face(LET_STMT, of(ASSIGN), EXPR_FIRST),
            new Face(LET_STMT, of(COLON), TYPE_FIRST),
            new Face(LET_DESTRUCTURE, of(LET_KW), PAT_FIRST),
            new Face(LET_DESTRUCTURE, PAT_LAST, of(ASSIGN)),
            new Face(LET_DESTRUCTURE, of(ASSIGN), EXPR_FIRST),
            new Face(GUARD_STMT, of(GUARD_KW), EXPR_FIRST),
            new Face(GUARD_STMT, EXPR_LAST, of(ELSE_KW, AS_KW)),
            new Face(GUARD_STMT, of(ELSE_KW), EXPR_FIRST),
            new Face(FN_DEF, of(LET_KW, IDENT), of(IDENT)),
            new Face(FN_DEF, of(IDENT), of(LPAREN, COLON, ASSIGN)),
            new Face(FN_DEF, of(RPAREN), of(COLON, ASSIGN)),
            new Face(FN_DEF, TYPE_LAST, of(ASSIGN)),
            new Face(FN_DEF, of(COLON), TYPE_FIRST),
            new Face(FN_DEF, of(ASSIGN), EXPR_FIRST),
            new Face(PARAM, of(IDENT), of(COLON)),
            new Face(PARAM, of(COLON), TYPE_FIRST),
            new Face(FN_PARAM, of(IDENT), of(COLON)),
            new Face(FN_PARAM, PAT_LAST, of(COLON)),
            new Face(FN_PARAM, of(COLON), TYPE_FIRST),
            new Face(FIELD, of(IDENT), of(COLON)),
            new Face(FIELD, of(COLON), TYPE_FIRST),
            new Face(FIELD, TYPE_LAST, of(QUESTION)),
            new Face(TYPE_REF, of(IDENT), of(LT)),
            new Face(TYPE_ARGS, of(LT), TYPE_FIRST),
            new Face(TYPE_ARGS, TYPE_LAST, of(GT, COMMA)),
            new Face(TYPE_ARGS, of(COMMA), TYPE_FIRST),
            new Face(TUPLE_TYPE, of(LPAREN), TYPE_FIRST),
            new Face(TUPLE_TYPE, TYPE_LAST, of(RPAREN, COMMA)),
            new Face(TUPLE_TYPE, of(COMMA), TYPE_FIRST),
            new Face(FN_TYPE, of(LPAREN), TYPE_FIRST),
            new Face(FN_TYPE, TYPE_LAST, of(RPAREN, COMMA)),
            new Face(FN_TYPE, of(COMMA), TYPE_FIRST),
            new Face(FN_TYPE, of(RPAREN), of(ARROW)),
            new Face(FN_TYPE, of(ARROW), TYPE_FIRST),
            new Face(RET_TYPE, TYPE_LAST, of(PIPE, QUESTION)),
            new Face(RET_TYPE, of(PIPE), TYPE_FIRST),
            new Face(PARAM_LIST, of(LPAREN), of(IDENT, RPAREN)),
            new Face(PARAM_LIST, TYPE_LAST, of(RPAREN, COMMA)),
            new Face(PARAM_LIST, of(COMMA), of(IDENT)),
            new Face(FN_PARAM_LIST, of(LPAREN, COMMA), PAT_FIRST),
            new Face(FN_PARAM_LIST, PAT_LAST, of(RPAREN, COMMA)),
            new Face(FN_PARAM_LIST, TYPE_LAST, of(RPAREN, COMMA)),
            new Face(PATTERN_TUPLE, of(LPAREN, COMMA), PAT_FIRST),
            new Face(PATTERN_TUPLE, PAT_LAST, of(RPAREN, COMMA)),
            new Face(PATTERN_CTOR, of(IDENT), of(LPAREN)),
            new Face(PATTERN_CTOR, of(LPAREN), PAT_FIRST),
            new Face(PATTERN_CTOR, PAT_LAST, of(RPAREN)),
            new Face(PATTERN_RECORD, of(LBRACE, COMMA), of(IDENT, RBRACE)),
            new Face(PATTERN_RECORD, of(IDENT), of(RBRACE, COMMA, ASSIGN)),
            new Face(PATTERN_RECORD, of(ASSIGN), of(IDENT)),
            new Face(PRODUCT_BODY, of(LBRACE, COMMA), of(IDENT, SPREAD)),
            new Face(SPREAD_MEMBER, of(SPREAD), of(IDENT)),
            new Face(SPREAD_MEMBER, of(IDENT), of(DOT)),
            new Face(SPREAD_MEMBER, of(DOT), of(IDENT)),
            new Face(ARG_LIST, of(LPAREN), of(RPAREN)),
            new Face(LIST_EXPR, of(LBRACKET), of(RBRACKET)),
            new Face(TUPLE_EXPR, of(LPAREN), of(RPAREN)),
            new Face(TUPLE_TYPE, of(LPAREN), of(RPAREN)),
            new Face(FN_TYPE, of(LPAREN), of(RPAREN)),
            new Face(PARAM_LIST, of(LPAREN), of(RPAREN)),
            new Face(FN_PARAM_LIST, of(LPAREN), of(RPAREN)),
            new Face(LAMBDA_EXPR, of(LPAREN), of(RPAREN)),
            new Face(PATTERN_TUPLE, of(LPAREN), of(RPAREN)),
            new Face(PATTERN_RECORD, of(LBRACE), of(RBRACE)),
            new Face(NEW_DATA_EXPR, of(LBRACE), of(RBRACE)),
            new Face(TYPE_ARGS, of(LT), of(GT)),
            // a match arm's pattern is a run of tokens, so the arm joins all of them
            new Face(MATCH_CASE, of(IDENT, RPAREN, RBRACE), of(DOT, LPAREN, LBRACE, PIPE, AS_KW,
                    COMMA, RBRACE, ASSIGN, IDENT)),
            new Face(MATCH_CASE, of(DOT, LPAREN, LBRACE, PIPE, AS_KW, COMMA, ASSIGN), of(IDENT)),
            new Face(MATCH_CASE, of(LPAREN), of(RPAREN)),
            new Face(MATCH_CASE, of(IDENT, RPAREN), of(RPAREN)),
            new Face(MATCH_EXPR, of(PIPE), of(IDENT)),
            new Face(PATTERN_FIELD, of(IDENT), of(ASSIGN)),
            new Face(PATTERN_FIELD, of(ASSIGN), of(IDENT)),
            new Face(MATCH_CASE, of(LBRACE), of(RBRACE)),
            // what a declaration writes around its own words
            new Face(MODULE_HEADER, of(MODULE_KW), of(IDENT)),
            new Face(MODULE_HEADER, of(IDENT), of(EXPOSING_KW)),
            new Face(EXPOSING_CLAUSE, of(EXPOSING_KW), of(LPAREN)),
            new Face(EXPOSING_CLAUSE, of(LPAREN, COMMA), of(IDENT)),
            new Face(EXPOSING_CLAUSE, of(IDENT, RPAREN, TYPEVAR, GT, QUESTION), of(RPAREN, COMMA)),
            new Face(EXPOSING_CLAUSE, of(LPAREN), of(RPAREN)),
            new Face(EXPOSED_ENTRY, of(IDENT), of(COLON)),
            new Face(EXPOSED_ENTRY, of(COLON), TYPE_FIRST),
            new Face(IMPORT_DECL, of(IMPORT_KW), of(IDENT)),
            new Face(IMPORT_DECL, of(IDENT), of(AS_KW, LPAREN)),
            new Face(IMPORT_ALIAS, of(AS_KW), of(IDENT)),
            new Face(NAME_LIST, of(LPAREN, COMMA), of(IDENT)),
            new Face(NAME_LIST, of(IDENT), of(RPAREN, COMMA)),
            new Face(NAME_LIST, of(LPAREN), of(RPAREN)),
            new Face(DATA_DEF, of(DATA_KW), of(IDENT)),
            new Face(DATA_DEF, of(IDENT), of(ASSIGN)),
            new Face(DATA_DEF, of(ASSIGN), of(IDENT, TYPEVAR, LPAREN, LBRACE)),
            new Face(PRODUCT_BODY, of(LBRACE), of(RBRACE)),
            new Face(SUM_BODY, of(IDENT), of(PIPE)),
            new Face(SUM_BODY, of(PIPE), of(IDENT)),
            new Face(INVARIANT_CLAUSE, of(INVARIANT_KW), EXPR_FIRST),
            new Face(INVARIANT_CLAUSE, of(IDENT), of(ASSIGN)),
            new Face(INVARIANT_CLAUSE, of(ASSIGN), EXPR_FIRST),
            new Face(BEHAVIOR_DEF, of(BEHAVIOR_KW), of(IDENT)),
            new Face(BEHAVIOR_DEF, of(IDENT), of(COLON, ASSIGN)),
            new Face(BEHAVIOR_DEF, of(COLON), of(LPAREN)),
            new Face(BEHAVIOR_DEF, of(ASSIGN), of(IDENT)),
            new Face(BEHAVIOR_SIG, of(RPAREN), of(ARROW)),
            new Face(BEHAVIOR_SIG, of(ARROW), TYPE_FIRST),
            new Face(CONSTRUCTS_CLAUSE, of(CONSTRUCTS_KW, COMMA), of(IDENT)),
            new Face(CONSTRUCTS_CLAUSE, of(IDENT), of(COMMA)),
            new Face(DEPENDS_CLAUSE, of(DEPENDS_KW, COMMA, IDENT), of(IDENT)),
            new Face(DEPENDS_CLAUSE, of(IDENT), of(COMMA)),
            new Face(PIPE_BEHAVIOR, of(IDENT), of(PIPEFWD, ARROW)),
            new Face(PIPE_BEHAVIOR, of(PIPEFWD, ARROW), of(IDENT)),
            new Face(FN_DEF, of(IDENT), of(LET_KW)),
            new Face(INTRINSIC_BODY, of(IDENT), of(STRING_LIT)),
            new Face(GUARD_STMT, of(AS_KW), of(IDENT)),
            new Face(IF_EXPR, of(AS_KW), of(IDENT)),
            new Face(ELSE_ARM, of(PIPE), of(IDENT)),
            new Face(ELSE_ARM, of(IDENT), of(ARROW)),
            new Face(ELSE_ARM, of(ARROW), EXPR_FIRST),
            new Face(EXAMPLES_FILE_HEADER, of(IDENT), of(IDENT)),
            new Face(EXAMPLE_DEF, of(IDENT), of(IDENT)),
            new Face(EXAMPLE_DEF, of(PIPE), of(STRING_LIT, LPAREN)),
            new Face(EXAMPLE_ROW, of(STRING_LIT), of(COLON)),
            new Face(EXAMPLE_ROW, of(COLON), of(LPAREN)),
            new Face(EXAMPLE_ROW, of(RPAREN), of(WITH_KW, ARROW)),
            new Face(EXAMPLE_ROW, EXPR_LAST, of(ARROW)),
            new Face(EXAMPLE_ROW, of(ARROW), EXPR_FIRST),
            new Face(WITH_CLAUSE, of(WITH_KW), of(IDENT)),
            new Face(WITH_CLAUSE, EXPR_LAST, of(COMMA)),
            new Face(WITH_CLAUSE, of(COMMA), of(IDENT)),
            new Face(WITH_BINDING, of(IDENT), of(ASSIGN)),
            new Face(WITH_BINDING, of(ASSIGN), EXPR_FIRST),
            new Face(FAKE_DEF, of(IDENT), of(IDENT)),
            new Face(FAKE_DEF, of(PIPE), of(LPAREN, IDENT)),
            new Face(FAKE_ROW, of(RPAREN, IDENT), of(ARROW)),
            new Face(FAKE_ROW, of(ARROW), EXPR_FIRST),
            new Face(QUALIFIED_NAME, of(IDENT), of(DOT)),
            new Face(QUALIFIED_NAME, of(DOT), of(IDENT)));


    /** Every boundary the domain holds, answered. */
    @Test
    void theRuleAnswersAllOfThem() {
        Set<String> unanswered = new TreeSet<>();
        for (Face f : DOMAIN) {
            for (SyntaxKind l : f.left()) {
                for (SyntaxKind r : f.right()) {
                    try {
                        Spacing.between(f.construct(), l, r);
                    } catch (IllegalStateException _) {
                        unanswered.add(f.construct() + ": " + l + " " + r);
                    }
                }
            }
        }
        assertEquals(new TreeSet<String>(), unanswered,
                "boundaries the grammar can build that the rule has no answer for");
    }

    /** And the domain holds every boundary the corpus reaches, so that it cannot quietly stop
     * being what the formatter writes. */
    @Test
    void andItHoldsEveryBoundaryTheCorpusReaches() {
        Set<String> outside = new TreeSet<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            for (Gaps.Boundary b : Gaps.boundaries(
                    Formatter.document(CstParser.parse(source).root()))) {
                if (b.joining() == null || b.policy() == TokenDoc.Break.ALWAYS) {
                    continue;   // not one the rule was asked about
                }
                if (!held(b.joining(), b.left(), b.right())) {
                    outside.add(b.joining() + ": " + b.left() + " " + b.right());
                }
            }
        }
        assertEquals(new TreeSet<String>(), outside,
                "boundaries the formatter writes that the domain above does not hold");
    }

    private static boolean held(SyntaxKind construct, SyntaxKind left, SyntaxKind right) {
        for (Face f : DOMAIN) {
            if (f.construct() == construct && f.left().contains(left) && f.right().contains(right)) {
                return true;
            }
        }
        return false;
    }
}
