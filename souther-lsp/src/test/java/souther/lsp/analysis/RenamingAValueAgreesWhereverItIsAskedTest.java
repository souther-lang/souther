package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What renaming edits does not depend on where the cursor was when it was asked.
 *
 * <p>A behavior is declared twice — the {@code behavior} line says what it is, the {@code let} line
 * says what it does — and both write its name. A value's binding is one place, and a use of it is
 * another; asking from either is asking about the same binding.
 *
 * <p>Both directions used to go through matching the spelling, which is blind to which binding a
 * name belongs to but does at least see every line the name is written on. Answering from
 * resolution has to keep that: an answer that rewrites one of a behavior's two declaration lines
 * leaves the module naming something that is no longer there.
 */
class RenamingAValueAgreesWhereverItIsAskedTest {

    private static final String URI = "file:///a.sou";

    /**
     * `g` is declared on line 3 at column 10 and on line 4 at column 5, and used on line 7 at
     * column 13. `x` is bound on line 8 at column 9 and used on line 9 at column 5.
     */
    private static final String SOURCE = """
            module a exposing ( N, g )

            behavior g : (n: N) -> N
            let g (n) = n

            behavior h : (n: N) -> N
            let h (n) = g({
                let x = n
                x
            })

            data N = { v: Int }
            """;

    private static Map<String, List<Range>> renameFrom(Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, SOURCE);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.renameEdits(URI, pos, graph);
    }

    /** The lines an edit set touches, as `line:character`, sorted. */
    private static Set<String> places(Map<String, List<Range>> edits) {
        Set<String> out = new TreeSet<>();
        edits.forEach((uri, ranges) -> ranges.forEach(r ->
                out.add(r.start().line() + ":" + r.start().character())));
        return out;
    }

    @Test
    void renamingABehaviorFromItsSignatureRewritesBothOfItsDeclarations() {
        Set<String> found = places(renameFrom(new Position(2, 9)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found,
                "the `exposing` entry, both declaration lines and the one use");
    }

    @Test
    void renamingABehaviorFromItsBodyRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(3, 4)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found);
    }

    @Test
    void renamingABehaviorFromAUseRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(6, 12)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found,
                "a use is a use of both declarations, not of the signature alone");
    }

    @Test
    void renamingALocalFromItsUseRewritesTheBindingToo() {
        Set<String> found = places(renameFrom(new Position(8, 4)));

        assertEquals(Set.of("7:8", "8:4"), found, "the `let x` and the `x` that reads it");
    }

    @Test
    void renamingALocalFromItsBindingRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(7, 8)));

        assertEquals(Set.of("7:8", "8:4"), found,
                "a binding is what its uses denote, whichever end the question comes from");
    }

    /** Line 3 writes the getter `.v` at column 36; a field getter desugars to a parameter nobody
     * wrote, three characters wide, anchored there. */
    private static final String GETTER = """
            module b exposing ( D, total )

            data D = { v: Int }

            behavior total : (ds: List<D>) -> Int
            let total (ds) = List.sum(List.map(.v, ds))
            """;

    private static Map<String, List<Range>> renameInGetter(Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///b.sou", GETTER);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.renameEdits("file:///b.sou", pos, graph);
    }

    @Test
    void aGetterIsNotSomethingToRename() {
        assertEquals(Map.of(), renameInGetter(new Position(5, 35)),
                "the `.` of `.v` names nothing an author can rename");
        assertEquals(Map.of(), renameInGetter(new Position(5, 36)), "nor its field");
    }

    @Test
    void aFieldIsNotSomethingToRenameEither() {
        assertEquals(Map.of(), renameInGetter(new Position(2, 11)),
                "renaming `v` here would rewrite the declaration and leave every read of it");
    }

    /**
     * The three forms where a pattern is lowered away: a parameter destructured into fields, a
     * {@code match} arm's fields, and a newtype opened by name. Each binds a name the author wrote
     * and holds the value in one nobody did.
     *
     * <p>Line 6 binds `l` at column 20 and `right` at column 23, and reads them at 32 and 36. Line 9
     * binds `f` at column 14 and reads it at 21. Line 16 binds `inner` at column 18 and reads it at
     * 28.
     */
    private static final String PATTERNS = """
            module c exposing ( Pair, Flat, Amount, pick, tag, held )

            data Pair = { left: Int, right: Int }
            data Flat = { f: Int }

            behavior pick : (p: Pair) -> Int
            let pick ({ left = l, right }) = l + right

            behavior tag : (x: Flat) -> Int
            let tag (x) = match x with
                | Flat { f } -> f

            data Amount = Int

            behavior held : (a: Amount) -> Int
            let held (Amount(inner)) = inner
            """;

    private static Set<String> renameInPatterns(Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///c.sou", PATTERNS);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return places(analyzer.renameEdits("file:///c.sou", pos, graph));
    }

    @Test
    void aNameBoundByARecordPatternIsRenameableFromEitherEnd() {
        assertEquals(Set.of("6:19", "6:33"), renameInPatterns(new Position(6, 19)),
                "`{ left = l }` binds `l`, and the body reads it");
        assertEquals(Set.of("6:19", "6:33"), renameInPatterns(new Position(6, 33)));
    }

    @Test
    void andSoIsTheShorthandThatBindsTheFieldsOwnName() {
        assertEquals(Set.of("6:22", "6:37"), renameInPatterns(new Position(6, 22)),
                "`{ right }` binds `right` at the field's own token");
        assertEquals(Set.of("6:22", "6:37"), renameInPatterns(new Position(6, 37)));
    }

    @Test
    void aMatchArmsFieldDestructuringIsRenameableFromEitherEnd() {
        assertEquals(Set.of("10:13", "10:20"), renameInPatterns(new Position(10, 13)),
                "`| Flat { f } -> f`");
        assertEquals(Set.of("10:13", "10:20"), renameInPatterns(new Position(10, 20)));
    }

    @Test
    void soIsANameANewtypePatternOpens() {
        assertEquals(Set.of("15:17", "15:27"), renameInPatterns(new Position(15, 17)),
                "`let held (Amount(inner)) = inner`");
        assertEquals(Set.of("15:17", "15:27"), renameInPatterns(new Position(15, 27)));
    }

    @Test
    void andThePatternItselfCarriesNothingToRename() {
        assertEquals(Set.of(), renameInPatterns(new Position(6, 10)),
                "the `{` of the destructured parameter holds a name nobody wrote");
    }

    @Test
    void thePatternsTypeNameIsThatTypeAndNotWhateverTheParameterIsCalled() {
        Set<String> found = renameInPatterns(new Position(15, 10));

        assertTrue(found.contains("12:5"), "`Amount(...)` names the type declared there: " + found);
        assertFalse(found.contains("15:17"), "and not the name the pattern binds: " + found);
    }
}
