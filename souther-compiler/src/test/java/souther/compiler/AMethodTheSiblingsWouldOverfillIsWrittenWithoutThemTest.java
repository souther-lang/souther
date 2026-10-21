package souther.compiler;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.ReplacementEvidence;
import souther.compiler.query.Replacements;
import souther.compiler.query.Weakening;
import souther.compiler.source.SourceId;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Measuring a model never makes it a model that does not compile.
 *
 * <p>The siblings an arm is run with in its place are this compiler's, written into the classes a
 * measurement runs in. A body the JVM holds as written can be one it does not hold with every arm's
 * siblings beside it — how large a method may be is a question about the whole method, and no count
 * at one fork answers it. So where the writer refuses a method for its size while it carries
 * siblings, it is written again without them, and the rewrites there are said to be ones the classes
 * could not carry.
 *
 * <p>The body here is four forks of two arms, each arm a sum of hundreds of terms: as written it is
 * a method the JVM holds, and with the siblings beside every arm it is not. Each arm is well under
 * what one fork may carry, so it is the method and not the fork that has no room.
 *
 * <p>The terms are decimals. A product of decimals runs past no end of a type, so a run past one
 * holds nothing it did not hold before it, and the bytes each term is written in fill the method
 * with nothing for a reading of the paths to take in term by term.
 */
class AMethodTheSiblingsWouldOverfillIsWrittenWithoutThemTest {

    private static final int FORKS = 4;

    private static final int TERMS = 350;

    private static String model() {
        StringBuilder body = new StringBuilder();
        StringBuilder sum = new StringBuilder();
        for (int f = 0; f < FORKS; f++) {
            StringBuilder held = new StringBuilder();
            StringBuilder other = new StringBuilder();
            for (int t = 1; t <= TERMS; t++) {
                held.append(t == 1 ? "" : ", ").append("x * ").append(t).append(".0m");
                other.append(t == 1 ? "" : ", ").append("x * ").append(t + 1000).append(".0m");
            }
            body.append("    let a").append(f).append(" = if x > ").append(f)
                    .append(".0m then List.sum([").append(held).append("]) else List.sum([")
                    .append(other).append("])\n");
            sum.append(f == 0 ? "" : " + ").append("a").append(f);
        }
        // At nought every fork takes its second arm and every term is nought; at nine every fork
        // takes its first, and each sums nine times one to three hundred and fifty.
        long atNine = (long) FORKS * 9 * TERMS * (TERMS + 1) / 2;
        return """
                module example.wide

                behavior f : (x: Decimal) -> Decimal

                let f (x) = {
                %s
                    %s
                }

                example f
                    | (0.0m) -> 0.0m
                    | (9.0m) -> %d.0m
                """.formatted(body, sum, atNine);
    }

    private static Compilation measured;

    /**
     * The model measured, once for the class. Every test here reads what one measurement of it
     * says, and none changes it; asked where the first test asks it rather than when the class is
     * loaded, so a model that fails to measure fails the test that asked and not the class.
     *
     * <p>Its classes and its examples are asked, which is what says whether it compiles and runs.
     * The warnings are not: none is read here, and the reachability of every path through the
     * sums is most of what asking them would cost.
     */
    private static Compilation measured() {
        if (measured == null) {
            Compilation compilation = Compilation.ofSource(model(), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.db().ask(new Output.All());
            for (String module : compilation.modules()) {
                for (SourceId id : compilation.exampleSourcesOf(module)) {
                    compilation.db().ask(Output.Examples.asked(compilation.db(), module, id));
                }
            }
            measured = compilation;
        }
        return measured;
    }

    /** And given back when the class is done with it: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        measured = null;
    }

    @Test
    void aMeasuredBuildOfABodyTheJvmHoldsCompiles() {
        Compilation compilation = measured();

        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the body compiles as written, and measuring it changes nothing about that");
    }

    /**
     * And the rewrites at the forks the method had no room for are left open as ones the classes
     * could not carry. Were they carried, this model would be one the method has room for, and the
     * test above would be asking nothing.
     */
    @Test
    void theRewritesTheClassesCouldNotCarryAreSaidToBeThose() {
        Compilation compilation = measured();
        Map<String, ReplacementEvidence> measured = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().getFirst())).value();

        List<ReplacementEvidence.Rewrite> rewrites = measured.get("f").measured().made()
                .orElseThrow(() -> new AssertionError("the rewrites were measured: " + measured))
                .rewrites();
        assertTrue(rewrites.stream().anyMatch(each -> each.outcome()
                        instanceof ReplacementEvidence.Undecided(var why)
                        && why.reasons().written()
                                .contains(ReplacementEvidence.Undecided.Why.TOO_LARGE)),
                () -> "a rewrite the method had no room for: " + rewrites);
    }

    /**
     * And the room was the JVM's, which no run of this compiler widens: every rewrite left open
     * for it is one a wider run leaves open too, and names no figure for a reader to raise.
     */
    @Test
    void aRewriteTheJvmHadNoRoomForIsOneNoWiderRunAnswers() {
        Compilation compilation = measured();
        ReplacementEvidence measured = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().getFirst())).value().get("f");

        List<Weakening> tooLarge = measured.measured().weakening().causes().stream()
                .filter(each -> each instanceof Weakening.RewriteUndecided it
                        && it.why().reasons().written()
                                .contains(ReplacementEvidence.Undecided.Why.TOO_LARGE))
                .toList();
        assertFalse(tooLarge.isEmpty(), () -> "a rewrite the method had no room for: " + measured);
        for (Weakening each : tooLarge) {
            assertEquals(RunSensitivity.UNAFFECTED, each.runSensitivity(), each::toString);
            assertEquals(List.of(), each.figures(), each::toString);
        }
    }
}
