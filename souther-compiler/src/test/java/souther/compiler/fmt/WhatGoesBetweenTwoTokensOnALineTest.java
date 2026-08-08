package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.Reserved;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the canonical form writes between two code tokens that share a line, as a function and not as
 * an observation. Three things, in order.
 *
 * <p><b>The range.</b> There is no third answer: whatever the source wrote between two tokens, the
 * canonical form writes nothing or one space. That is where the alignment goes.
 *
 * <p><b>The rule.</b> Which of the two is decided by the construct that joins the tokens — their
 * lowest common ancestor in the tree — together with the kind on each side. Over a corpus that builds
 * every kind of node the grammar has, that key never takes both answers. So the function exists, and
 * this is what it reads.
 *
 * <p><b>Where the construct is load-bearing.</b> For all but nine pairs of token kinds the answer is
 * the same from every construct that can join them, so the pair alone decides. The nine are written
 * out below with each construct's answer, and they are the whole of what a rule for this has to say
 * about position. The remaining two hundred are not transcribed: they are pinned by the rule and by
 * the coverage above it, and a listing of them would freeze the corpus rather than state a rule.
 *
 * <p>The corpus is not a sample of Souther. It is a set of sources chosen so that every node kind in
 * {@link SyntaxKind} is built at least once, and that is asserted — a kind added to the grammar
 * without a source here fails rather than going unmeasured.
 */
class WhatGoesBetweenTwoTokensOnALineTest {

    /** Sources written to reach the constructs the bundled standard library does not use. */
    private static final List<String> WRITTEN = List.of(
            """
            module m exposing ( f, T )

            import some.place as P ( alpha )

            behavior pay : (a: Amount, b: Int) -> Paid | Refused
                depends on clock, audit
                constructs Paid, Refused
            """,
            """
            module m

            data W = Int

            let f (w: W): Int = {
                let W(inner) = w
                let (x, y) = pair
                let { a, b = c } = record
                guard Amount(inner) as amount else
                    | one -> Refused
                    | two -> Denied
                amount
            }
            """,
            """
            module m

            data A

            data B

            let f (o: Option<W>): Int = match o with
                | Some(W(x)) -> x
                | Mod.None { a, b = c } as whole -> 0
                | A | B -> unreachable "neither reaches this rule"
            """,
            """
            module m

            let f (a: Int, g: (Int, Int) -> Int, t: (Int, Int)): Int = -(a + 1) * g(1, 2)
            """,
            """
            module m

            let f (a: Int?): Int = if a > 0 then 1 else 0

            let each (xs: List<Int>): List<Int> = [x | x > 0]

            let by: (W) -> Int = .value

            let piped (a: Int): Int = a |> double |> triple

            partial let part (a: Int): Int = a

            private let hidden (a: Int): Int = a
            """,
            """
            module m

            data P =
                { a: Int
                }

            data Q =
                { ...P
                , b: Int
                }

            data S = A | B

            data N = Int
                invariant value >= 0

            let f (p: P): Q = Q { ...p, b = 1 }
            """,
            """
            module m exposing ( sized : (Int) -> Int, T )

            let sized (n: Int): Int = -n

            let cmp (a: Int, b: Int): Bool = double(a) > b
            """,
            """
            module m

            behavior b = alpha >-> beta -> Int
            """,
            """
            examples for m

            example helper
                | "a description" : (1) with dep = two, other = three -> 2

            fake helper
                | (1) -> 2
                | _ -> 0
            """);

    private static String stdlib(String module) {
        String resource = "/souther/" + module + ".sou";
        try (InputStream in = WhatGoesBetweenTwoTokensOnALineTest.class.getResourceAsStream(resource)) {
            assertTrue(in != null, "missing bundled source " + resource);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Every source the rule is read from: the bundled standard library, and the written sources. */
    static List<String> corpus() {
        List<String> out = new ArrayList<>();
        for (Reserved.StdlibModule m : Reserved.MODULES) {
            out.add(stdlib(m.moduleName().substring("souther.".length())));
        }
        out.addAll(WRITTEN);
        return out;
    }

    private static List<SyntaxToken> tokens(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                out.addAll(tokens(c));
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
        return out;
    }

    private static void nodeKindsOf(SyntaxNode n, Set<SyntaxKind> out) {
        out.add(n.kind());
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                nodeKindsOf(c, out);
            }
        }
    }

    /** The construct that joins two tokens: the deepest node holding both of them. */
    private static SyntaxNode joining(SyntaxToken left, SyntaxToken right) {
        Set<SyntaxNode> above = new LinkedHashSet<>();
        for (SyntaxNode p = left.parent(); p != null; p = p.parent()) {
            above.add(p);
        }
        for (SyntaxNode p = right.parent(); p != null; p = p.parent()) {
            if (above.contains(p)) {
                return p;
            }
        }
        throw new AssertionError("two tokens of one file with no node holding both");
    }

    /** One adjacency in a canonical form: what joins the two tokens, their kinds, and what is
     * written between them. */
    record Adjacency(SyntaxKind joins, SyntaxKind left, SyntaxKind right, String separator) {
        String pair() {
            return left + " " + right;
        }
    }

    /** Every adjacency in the canonical form of every source, excluding the pairs a break separated,
     * which are the other rules' business. */
    private static List<Adjacency> adjacencies() {
        List<Adjacency> out = new ArrayList<>();
        for (String source : corpus()) {
            String canonical = Formatter.format(source);
            CstParser.Result parsed = CstParser.parse(canonical);
            assertTrue(parsed.errors().isEmpty(), "a canonical form did not reparse:\n" + canonical);
            List<SyntaxToken> code = tokens(parsed.root()).stream().filter(t -> !t.isTrivia()).toList();
            for (int i = 0; i + 1 < code.size(); i++) {
                SyntaxToken a = code.get(i);
                SyntaxToken b = code.get(i + 1);
                String gap = canonical.substring(a.end(), b.start());
                if (!gap.contains("\n")) {
                    out.add(new Adjacency(joining(a, b).kind(), a.kind(), b.kind(), gap));
                }
            }
        }
        return out;
    }

    // --- the range ---

    /** Nothing, or one space. Alignment is what this rules out: a column of `=` signs lined up under
     * each other needs a run of spaces between two tokens, and no such run survives. */
    @Test
    void whatIsWrittenBetweenThemIsNothingOrOneSpace() {
        Set<String> seen = new LinkedHashSet<>();
        adjacencies().forEach(a -> seen.add(a.separator()));
        assertTrue(Set.of("", " ").containsAll(seen), "the separators written are " + seen);
    }

    /** And both of them are written, so the rule below has two answers to choose between. */
    @Test
    void andBothOfThemAreWritten() {
        Set<String> seen = new LinkedHashSet<>();
        adjacencies().forEach(a -> seen.add(a.separator()));
        assertEquals(Set.of("", " "), seen, "over the whole corpus");
    }

    // --- the rule ---

    /**
     * The construct that joins the two tokens, and the kind on each side, decide what goes between
     * them. Nothing else is read: no two adjacencies with that key are written differently.
     */
    @Test
    void theConstructThatJoinsThemAndTheirKindsDecideIt() {
        Map<String, Set<String>> answers = new LinkedHashMap<>();
        for (Adjacency a : adjacencies()) {
            answers.computeIfAbsent(a.joins() + " " + a.pair(), _ -> new LinkedHashSet<>())
                    .add(a.separator());
        }
        List<String> disagreeing = answers.entrySet().stream()
                .filter(e -> e.getValue().size() > 1)
                .map(e -> e.getKey() + " -> " + e.getValue()).toList();
        assertEquals(List.of(), disagreeing, "keys written both ways");
    }

    // --- where the construct is load-bearing ---

    /**
     * The pairs of token kinds whose answer the joining construct decides, and what each construct
     * answers. Every other pair takes one answer wherever it occurs.
     */
    private static final Map<String, Map<String, String>> POSITION_DECIDES = positionDecides();

    /** A row: the constructs that can join this pair, each with what it writes between them. */
    private static Map<String, String> row(String... constructAndSeparator) {
        Map<String, String> out = new LinkedHashMap<>();
        for (int i = 0; i < constructAndSeparator.length; i += 2) {
            out.put(constructAndSeparator[i], constructAndSeparator[i + 1]);
        }
        return out;
    }

    private static Map<String, Map<String, String>> positionDecides() {
        Map<String, Map<String, String>> out = new LinkedHashMap<>();
        // A list of names is written open — `exposing ( a, b )`, `import m ( a, b )` — and every
        // other bracketed construct is not.
        out.put("LPAREN IDENT", row(
                "EXPOSING_CLAUSE", " ", "NAME_LIST", " ",
                "ARG_LIST", "", "PARAM_LIST", "", "FN_PARAM_LIST", "", "FN_TYPE", "",
                "LAMBDA_EXPR", "", "MATCH_CASE", "", "PAREN_EXPR", "", "PATTERN_CTOR", "",
                "PATTERN_TUPLE", "", "TUPLE_EXPR", "", "TUPLE_TYPE", ""));
        out.put("IDENT RPAREN", row(
                "EXPOSING_CLAUSE", " ", "NAME_LIST", " ",
                "ARG_LIST", "", "PARAM_LIST", "", "FN_PARAM_LIST", "", "FN_TYPE", "",
                "LAMBDA_EXPR", "", "MATCH_CASE", "", "PATTERN_CTOR", "", "PATTERN_TUPLE", "",
                "TUPLE_EXPR", "", "TUPLE_TYPE", ""));
        // A declaration's name is spaced from what follows it; what is applied or opened is not.
        out.put("IDENT LPAREN", row(
                "FN_DEF", " ", "IMPORT_DECL", " ",
                "APPLY_EXPR", "", "MATCH_CASE", "", "PATTERN_CTOR", ""));
        // A type ascribed to a name is written tight against it; a signature is spaced from its name.
        out.put("IDENT COLON", row(
                "BEHAVIOR_DEF", " ", "EXPOSED_ENTRY", " ",
                "FIELD", "", "FN_DEF", "", "FN_PARAM", "", "PARAM", ""));
        // `<` and `>` are a type's brackets or a comparison's operator.
        out.put("IDENT LT", row("TYPE_REF", "", "BINARY_EXPR", " "));
        out.put("LT IDENT", row("TYPE_ARGS", "", "BINARY_EXPR", " "));
        out.put("IDENT GT", row("TYPE_ARGS", "", "BINARY_EXPR", " "));
        out.put("RPAREN GT", row("TYPE_ARGS", "", "BINARY_EXPR", " "));
        // `-` negates or subtracts.
        out.put("MINUS IDENT", row("UNARY_EXPR", "", "BINARY_EXPR", " "));
        return out;
    }

    /** These pairs, and no others, are written both ways somewhere in the corpus. */
    @Test
    void theseArePairsTheJoiningConstructDecides() {
        Map<String, Set<String>> byPair = new LinkedHashMap<>();
        for (Adjacency a : adjacencies()) {
            byPair.computeIfAbsent(a.pair(), _ -> new LinkedHashSet<>()).add(a.separator());
        }
        Set<String> both = new TreeSet<>();
        byPair.forEach((k, v) -> {
            if (v.size() > 1) {
                both.add(k);
            }
        });
        assertEquals(new TreeSet<>(POSITION_DECIDES.keySet()), both);
    }

    /** And each construct that joins one of them writes what the table says. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("decidedPairs")
    void andEachConstructAnswersAsTheTableSays(String pair) {
        Map<String, String> expected = POSITION_DECIDES.get(pair);
        Map<String, String> seen = new LinkedHashMap<>();
        for (Adjacency a : adjacencies()) {
            if (a.pair().equals(pair)) {
                seen.put(a.joins().name(), a.separator());
            }
        }
        assertEquals(new TreeSet<>(expected.keySet()), new TreeSet<>(seen.keySet()),
                pair + ": the constructs that join this pair");
        expected.forEach((construct, separator) ->
                assertEquals(separator, seen.get(construct), pair + " under " + construct));
    }

    static Stream<String> decidedPairs() {
        return POSITION_DECIDES.keySet().stream();
    }

    /**
     * The same pattern, written as a match arm and as a {@code let}. The grammar writes a match arm's
     * pattern as a run of tokens rather than as a node, so the formatter joins those tokens itself
     * instead of a construct writing what goes between them — the one place in the formatter where
     * that happens. It has to answer as the construct that writes the same syntax elsewhere does, or
     * the same pattern reads two ways depending on where it is.
     *
     * <p>It did not: a newtype opened by its constructor was written {@code Some ( x )} in a match
     * arm and {@code Some(x)} in a {@code let}, and no fixture in the suite observed the difference.
     */
    @Test
    void aPatternReadsTheSameWhereverItIsWritten() {
        String canonical = Formatter.format("""
                module m

                data W = Int

                let opened (o: Option<W>): Int = match o with
                    | Some(W(x)) -> x
                    | Held { a, b = c } -> a
                    | None -> 0

                let bound (w: W): Int = {
                    let W(inner) = w
                    let { a, b = c } = inner
                    a
                }
                """);
        for (String written : List.of(
                "| Some(W(x)) -> x", "let W(inner) = w",
                "| Held { a, b = c } -> a", "let { a, b = c } = inner")) {
            assertTrue(canonical.contains(written),
                    "nothing holds `" + written + "` in:\n" + canonical);
        }
    }

    // --- the corpus covers the grammar ---

    /**
     * Every node kind the grammar builds occurs in the corpus. Without this the rule above is a
     * statement about the sources that happened to be read: a construct absent from all of them
     * could join two tokens in a way nothing here would have seen.
     */
    @Test
    void thereIsASourceForEveryKindOfNode() {
        Set<SyntaxKind> built = new LinkedHashSet<>();
        for (String source : corpus()) {
            nodeKindsOf(CstParser.parse(Formatter.format(source)).root(), built);
        }
        Set<String> missing = new TreeSet<>();
        for (SyntaxKind k : SyntaxKind.values()) {
            if (k.ordinal() >= SyntaxKind.SOURCE_FILE.ordinal() && !built.contains(k)) {
                missing.add(k.name());
            }
        }
        assertEquals(new TreeSet<String>(), missing, "node kinds no source in the corpus builds");
    }

    /**
     * The node kinds that never join two tokens on a line, which is why they name no row above. Each
     * either holds one token, or writes a break between every two it holds. Listed rather than left
     * out, so that one which starts joining tokens is noticed.
     */
    @Test
    void andTheseKindsOfNodeJoinNoTwoTokensOnALine() {
        Set<SyntaxKind> built = new LinkedHashSet<>();
        for (String source : corpus()) {
            nodeKindsOf(CstParser.parse(Formatter.format(source)).root(), built);
        }
        Set<String> joins = new TreeSet<>();
        adjacencies().forEach(a -> joins.add(a.joins().name()));
        Set<String> never = new TreeSet<>();
        built.forEach(k -> {
            if (!joins.contains(k.name())) {
                never.add(k.name());
            }
        });
        assertEquals(new TreeSet<>(List.of(
                "BLOCK_EXPR",          // its statements are one to a line
                "ELSE_ARMS",           // its arms are one to a line
                "LITERAL_EXPR",        // one token
                "NEWTYPE_BODY",        // one type reference
                "PARTIAL_MODIFIER",    // one token
                "PATTERN_NAME",        // one token
                "PRIVATE_MODIFIER",    // one token
                "SOURCE_FILE",         // its items are one to a line
                "STAGE",               // one stage of a pipeline, one to a line
                "VAR_EXPR")),          // one token
                never);
    }
}
