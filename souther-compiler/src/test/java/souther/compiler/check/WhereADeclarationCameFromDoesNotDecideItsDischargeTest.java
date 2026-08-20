package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A construction is read against the same clauses wherever the type declaring them was written
 * (spec §invariant-discharge-representation).
 *
 * <p>Three provenances for one declaration: written in the module doing the constructing, imported
 * from a module compiled beside it, and imported from a module compiled on its own and reached
 * through nothing but its published classes. The clauses are the same clauses, so the verdicts are
 * the same verdicts — a guard that discharges an invariant discharges it, and one that leaves it
 * unproven leaves it unproven.
 *
 * <p>Held because the specification said otherwise. It said a clause arriving from another module
 * arrives as the computation it became and is outside the dischargeable fragment even where the same
 * clause written here would be inside it. Measured, all three of these discharge; the sentence
 * described a compiler that had already stopped being this one, and nothing failed when it stopped
 * (#722). Where a published declaration is put back together from is the compiler's business, and
 * this is what the language says instead.
 */
class WhereADeclarationCameFromDoesNotDecideItsDischargeTest {

    private static final String LIBRARY = """
            module lib
            exposing (Amount, Bag)

            data Amount = Decimal
                invariant nonNegative = value >= 0m

            data Bag = List<Int>
                invariant nonEmpty = List.length(value) >= 1
            """;

    /** The same declarations, written where they are used. */
    private static final String OWN = """
            data Amount = Decimal
                invariant nonNegative = value >= 0m

            data Bag = List<Int>
                invariant nonEmpty = List.length(value) >= 1
            """;

    private static final String USES = """
            data TooSmall

            behavior take : (paid: Decimal) -> Amount | TooSmall
                constructs Amount
            let take (paid) = {
                guard paid >= 0m else TooSmall
                Amount(paid)
            }

            behavior fill : (xs: List<Int>) -> Bag | TooSmall
                constructs Bag
            let fill (xs) = {
                guard List.length(xs) >= 1 else TooSmall
                Bag(xs)
            }
            """;

    /** Both constructions guarded, so both are established wherever the clauses came from. */
    @Test
    void aGuardEstablishesAnInvariantWhereverItWasDeclared() {
        assertEquals(List.of(Verdict.PROVED, Verdict.PROVED), inTheSameModule(USES));
        assertEquals(List.of(Verdict.PROVED, Verdict.PROVED), imported(USES));
        assertEquals(List.of(Verdict.PROVED, Verdict.PROVED), importedFromClasses(USES));
    }

    /** And neither guarded, so both are unproven wherever they came from — the same test with the
     * guards taken out, so that agreement is not agreement on silence. */
    @Test
    void anUnguardedConstructionIsUnprovenWhereverItWasDeclared() {
        String unguarded = """
                behavior take : (paid: Decimal) -> Amount
                    constructs Amount
                let take (paid) = Amount(paid)

                behavior fill : (xs: List<Int>) -> Bag
                    constructs Bag
                let fill (xs) = Bag(xs)
                """;

        assertEquals(List.of(Verdict.UNKNOWN, Verdict.UNKNOWN), inTheSameModule(unguarded));
        assertEquals(List.of(Verdict.UNKNOWN, Verdict.UNKNOWN), imported(unguarded));
        assertEquals(List.of(Verdict.UNKNOWN, Verdict.UNKNOWN), importedFromClasses(unguarded));
    }

    private static List<Verdict> inTheSameModule(String uses) {
        return verdicts(() -> Compiler.compileWithWarnings("module app\n\n" + OWN + "\n" + uses));
    }

    private static List<Verdict> imported(String uses) {
        return verdicts(() -> Compiler.compileModulesWithWarnings(
                List.of(LIBRARY, app(uses))));
    }

    /** The library compiled on its own, and its classes handed over as the whole of what the second
     * compile knows about it. */
    private static List<Verdict> importedFromClasses(String uses) {
        Map<String, byte[]> classes = Compiler.compile(LIBRARY);
        ModulePath path = classes::get;
        return verdicts(() -> Compiler.compileModulesWithWarnings(List.of(app(uses)), path));
    }

    private static String app(String uses) {
        return "module app\n\nimport lib ( Amount, Bag )\n\n" + uses;
    }

    private static List<Verdict> verdicts(Runnable compile) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            compile.run();
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> reached = said.stream()
                .filter(one -> one.type().equals("Amount") || one.type().equals("Bag"))
                .map(Said::verdict).toList();
        assertFalse(reached.isEmpty(), "no construction was judged at all");
        return reached;
    }
}
