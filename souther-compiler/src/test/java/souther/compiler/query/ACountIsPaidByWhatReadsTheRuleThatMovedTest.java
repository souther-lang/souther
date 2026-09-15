package souther.compiler.query;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeCardinality;
import souther.compiler.check.UninhabitableTypes;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a rule moving costs a count is what reads the rule, and not what the module holds beside it.
 *
 * <p>A count of a module answers about every declaration of it, so the question is asked again
 * whenever any of them is edited. What it costs to answer it again is the thing held here: the
 * declarations that read the rule that moved are answered afresh, and every other declaration of the
 * module is handed what it already came to, however many of them there are.
 *
 * <p>Counted in the askings of what a declaration comes to
 * ({@link TypeCardinality#transfersMade()}) rather than in the readings made. A reading is made once
 * per declaration per revision and lent to every count that wants it after, so a count that answered
 * the whole module again borrows one reading per declaration and the readings say nothing about it.
 * The askings are what a count spends.
 */
class ACountIsPaidByWhatReadsTheRuleThatMovedTest {

    private static final String MODULE = "chain.links";
    private static final String ID = "links.sou";

    /** Declarations the edits below say nothing about, each with rules of its own to be read. */
    private static String spares(int howMany) {
        StringBuilder source = new StringBuilder();
        for (int i = 0; i < howMany; i++) {
            source.append("data Spare").append(i).append(" = Int\n")
                    .append("    invariant value >= 1 && value <= 50\n");
        }
        return source.toString();
    }

    private static String names(String prefix, int howMany) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < howMany; i++) {
            out.append(prefix).append(i).append(", ");
        }
        return out.toString();
    }

    /** Two records over a newtype, and beside them declarations that read none of it. */
    private static String besideSpares(int howMany, int most) {
        return "module " + MODULE + " exposing ( Held, Holding, Tail, " + names("Spare", howMany)
                + "Nothing )\n\n"
                + "data Tail = Int\n    invariant value >= 1 && value <= " + most + "\n"
                + "data Held = { tail: Tail }\n"
                + "data Holding = { held: Held }\n"
                + "data Nothing = Int\n    invariant value >= 1\n"
                + spares(howMany);
    }

    /**
     * A chain of records with a rule at either end: {@code Tail}, which every link of the chain
     * reads, and {@code Mark}, which only the declaration at the top of it does.
     */
    private static String chain(int links, int tailMost, int markMost) {
        StringBuilder source = new StringBuilder();
        source.append("module ").append(MODULE).append(" exposing ( ")
                .append(names("Link", links)).append("Tail, Mark, Top )\n\n");
        source.append("data Tail = Int\n    invariant value >= 1 && value <= ")
                .append(tailMost).append("\n");
        source.append("data Mark = Int\n    invariant value >= 1 && value <= ")
                .append(markMost).append("\n");
        for (int i = 0; i < links; i++) {
            source.append("data Link").append(i).append(" = { next: ")
                    .append(i + 1 < links ? "Link" + (i + 1) : "Tail").append(" }\n");
        }
        return source.append("data Top = { link: Link0, mark: Mark }\n").toString();
    }

    private static Compilation compiling(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(ID, source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        return c;
    }

    /** What answering the module again costs once {@code edited} is what the documents hold. */
    private static long askingsFor(String written, String edited) {
        Compilation c = compiling(written);
        long before = TypeCardinality.transfersMade();
        c.update(Map.of(ID, edited), Set.of());
        c.answerEverything();
        return TypeCardinality.transfersMade() - before;
    }

    /**
     * A rule moving is paid for by what reads it, and the declarations beside it are not asked.
     *
     * <p>Held as one number at two sizes rather than as a slope, because what is claimed is that the
     * declarations an edit says nothing about have no part in it at all. A count that read half of
     * them would grow more slowly and would still be reading them.
     */
    @Test
    void aRuleMovingIsNotPaidForByTheDeclarationsBesideIt() {
        assertEquals(askingsFor(besideSpares(1, 99), besideSpares(1, 98)),
                askingsFor(besideSpares(32, 99), besideSpares(32, 98)),
                "a rule moved, and declarations that read none of it were answered again for it");
    }

    /**
     * And the same held of a chain: a rule nothing but the top of it reads costs what reads it,
     * however long the chain below is.
     */
    @Test
    void aRuleOnlyOneDeclarationReadsIsPaidForByThatOne() {
        assertEquals(askingsFor(chain(2, 99, 99), chain(2, 99, 98)),
                askingsFor(chain(32, 99, 99), chain(32, 99, 98)),
                "a rule read by one declaration was paid for by the length of a chain beside it");
    }

    /**
     * And the fixture can tell that from a rule every link does read, which every one of them is
     * answered again for.
     *
     * <p>The control. Without it the two above are held by a count that answers nothing at all,
     * which is not what is wanted of them: what a count owes is the declarations that read what
     * moved, and a chain every link of which reads the rule owes all of them.
     */
    @Test
    void aRuleEveryLinkReadsIsPaidForByEveryLink() {
        assertTrue(askingsFor(chain(32, 99, 99), chain(32, 98, 99))
                        > askingsFor(chain(2, 99, 99), chain(2, 98, 99)),
                "a rule every link of the chain reads was answered again for the links that read"
                        + " it, so the fixture cannot tell a declaration an edit reached from one it"
                        + " did not");
    }

    /**
     * And what the components came to is what one count of the whole module would have come to.
     *
     * <p>Of the report and not of every count. What a count is asked for is which declarations no
     * value satisfies, which of them are at fault for it together, and what shows it; a component
     * answered under the counts its own rules turn on may round a count some other declaration's
     * rule asked about differently, and no reader of this can tell.
     */
    @Test
    void whatTheComponentsCameToIsWhatOneCountOfTheModuleWouldHave() {
        for (String written : List.of(
                besideSpares(4, 99),
                chain(4, 99, 99),
                """
                module chain.links exposing ( Bad, Wanting, Pair, Fine )

                data Bad = Int
                    invariant value >= 2 && value <= 1
                data Wanting = { bad: Bad }
                data Pair = { one: Pair, two: Fine }
                data Fine = Int
                    invariant value >= 1 && value <= 9
                """)) {
            Compilation c = Compilation.ofDocuments(
                    new LinkedHashMap<>(Map.of(ID, written)), Set.of(), ModulePath.EMPTY);
            c.answerEverything();

            List<TypeSymbol.AtModule> declared =
                    c.db().ask(new Front.DeclaredTypes(MODULE)).value();
            RuleReadingSource source = Shapes.ruleReading(c.db(), MODULE).value();
            ReadingPolicy policy = c.db().ask(new Front.Reading()).value();
            TypeCardinality.Cardinalities whole = TypeCardinality.solve(
                    declared, source, policy, c.db().readings(),
                    TypeCardinality.Premises.read(source, policy, c.db().readings()));

            assertEquals(
                    new UninhabitableTypes.WithNoValue.Counted(
                            UninhabitableTypes.withNoValueOfTheirOwn(declared, whole)),
                    c.db().ask(new Shapes.TypesWithNoValue(MODULE)).value(),
                    () -> "the components came to something a count of the module would not have,"
                            + " for:\n" + written);
        }
    }
}
