package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Names;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Granting a declaration a value, held against every way another one reaches it.
 *
 * <p>What tells a lack of its own from one answering for another is the supposing: take a
 * declaration to have values and see what is still without them. The supposing is only as good as
 * the readings that honour it, and there are three of those.
 *
 * <pre>
 * the count       what the solution says of the name is UNKNOWN
 * the rules       the seeding stops at the name: neither what it wrote nor
 *                 anything guaranteed under it is read
 * the shape       the name is not opened onto what it wraps
 * </pre>
 *
 * <p>Which of them a model needs depends on how one declaration reaches another. A case of a sum and
 * a member of a union read the count and nothing else. A field, a value a collection holds, and a
 * count taken beside one go through the rules as well. A name worn over a value needs all three.
 *
 * <p>A reading that honours two of them undoes the supposing at the third, and what comes back is a
 * declaration reported for a lack that is not its own. So this is held of the reading rather than of
 * the report: each model below is one where the reader has no value while nothing is granted — the
 * row would say nothing otherwise — and a value once the one it reaches is granted one.
 */
class AGrantedNameIsReadAsGrantedWhereverItIsReachedTest {

    private static void grantingLeaves(String source, String granted, String reader) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        // Everything but the refusal these answers decide. A model refused for anything else is one
        // whose declarations were never read, and a name that is not declared is answered by the
        // absence of it rather than by anything here.
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code().toString())
                        .filter(each -> !each.equals("E1013")).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Names.derivedSymbols(compilation.db(), "demo").value();
        TypeCardinality.Cardinalities solved =
                TypeCardinality.solve(compilation.module("demo").defs().stream().map(Derived.Def::read).toList(), symbols);
        assertTrue(solved.of(TypeSymbols.declared(new TypeKey(symbols.module(), reader))).none(),
                "`" + reader + "` has no value while nothing is granted");
        assertFalse(solved.granting(Set.of(TypeSymbols.declared(new TypeKey(symbols.module(), granted))))
                        .get(TypeSymbols.declared(new TypeKey(symbols.module(), reader))).none(),
                "`" + reader + "` reaches `" + granted + "` and was granted it has values");
    }

    /** The name a value wears, which is the one place a name is opened rather than answered. */
    @Test
    void throughTheNameAValueWears() {
        grantingLeaves("""
                module demo

                data A = B
                data B = { a: A }
                """, "A", "B");
    }

    /** A field of a record. */
    @Test
    void throughAFieldOfARecord() {
        grantingLeaves("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data Holder = { x: Bad }
                """, "Bad", "Holder");
    }

    /** A case of a sum. */
    @Test
    void throughACaseOfASum() {
        grantingLeaves("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """, "Leaf", "Shape");
    }

    /** A value a collection holds, which the rules will not let be empty. */
    @Test
    void throughWhatACollectionHolds() {
        grantingLeaves("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data Holding = List<Bad>
                    invariant nonEmpty = List.length(value) >= 1
                """, "Bad", "Holding");
    }

    /**
     * And through a name that wrote no rule of its own, what it wraps having written one.
     *
     * <p>The row that tells the two questions apart. Leaving a granted declaration's own clauses out
     * is not enough where it wrote none: what says it has no value is written under it, and reading
     * that is the supposing undone by the walk that honoured it. Held with the one underneath left
     * as it is, so nothing passes by granting more than was asked.
     */
    @Test
    void throughANameThatWroteNoRuleOfItsOwn() {
        String source = """
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data Granted = Bad

                data Holder = { g: Granted }
                """;
        grantingLeaves(source, "Granted", "Holder");

        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Names.derivedSymbols(compilation.db(), "demo").value();
        assertTrue(TypeCardinality.solve(compilation.module("demo").defs().stream().map(Derived.Def::read).toList(), symbols)
                        .granting(Set.of(TypeSymbols.declared(new TypeKey(symbols.module(), "Granted")))).get(TypeSymbols.declared(new TypeKey(symbols.module(), "Bad"))).none(),
                "and what it wraps was not granted anything");
    }

    /** And through a count: what is absent leaves one value, and one is too few to fill a set. */
    @Test
    void throughHowManyValuesSomethingBesideItHas() {
        grantingLeaves("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data MaybeBad = { x: Bad? }

                data NeedTwo = Set<MaybeBad>
                    invariant two = Set.size(value) >= 2
                """, "Bad", "NeedTwo");
    }

    /** Nothing is granted while the counts themselves are read, so the reading is what it was. */
    @Test
    void nothingIsGrantedWhileTheCountsAreRead() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data A = B
                data B = { a: A }
                """, "Main");
        compilation.answerEverything();
        Symbols symbols = Names.derivedSymbols(compilation.db(), "demo").value();
        TypeCardinality.Cardinalities solved =
                TypeCardinality.solve(compilation.module("demo").defs().stream().map(Derived.Def::read).toList(), symbols);

        assertEquals(List.of(true, true),
                List.of(solved.of(TypeSymbols.declared(new TypeKey(symbols.module(), "A"))).none(),
                        solved.of(TypeSymbols.declared(new TypeKey(symbols.module(), "B"))).none()),
                "neither of them can be built");
    }
}
