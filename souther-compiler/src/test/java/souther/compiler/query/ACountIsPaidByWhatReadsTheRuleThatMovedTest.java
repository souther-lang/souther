package souther.compiler.query;

import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
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

    /**
     * How long the chain below the rule is, where the claim is that it makes no difference.
     *
     * <p>Kept short because a chain is what a compile is slowest at: a field read through one is
     * read at every depth it reaches, and what that costs rises with the depth far faster than with
     * the declarations. Long enough that a count paying by the module rather than by what reads the
     * rule is told apart several times over, and no longer.
     */
    private static final int LONG = 10;

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
     * And the same over a chain, where which rule moved is what decides who pays.
     *
     * <p>Both rules in one test because neither says anything alone. That the rule only the top of
     * the chain reads costs the same however long the chain is, is the claim; that the rule every
     * link reads costs more as the chain grows is what says the fixture can tell a declaration the
     * edit reached from one it did not. Held apart from a count that answers nothing at all only by
     * the second.
     */
    @Test
    void whichRuleMovedIsWhatDecidesWhoPaysForIt() {
        long shortChain = askingsFor(chain(2, 99, 99), chain(2, 99, 98));
        long longChain = askingsFor(chain(LONG, 99, 99), chain(LONG, 99, 98));

        assertEquals(shortChain, longChain,
                "a rule read by one declaration was paid for by the length of a chain beside it");
        assertTrue(askingsFor(chain(LONG, 99, 99), chain(LONG, 98, 99)) > longChain,
                "a rule every link of the chain reads cost no more than one only the top reads, so"
                        + " the fixture cannot tell a declaration an edit reached from one it did"
                        + " not");
    }

}
