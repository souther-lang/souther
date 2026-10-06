package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReplacementEvidence;
import souther.compiler.query.Replacements;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * a method the JVM holds, and five such forks are not. Each arm is well under what one fork may
 * carry, so it is the method and not the fork that has no room.
 */
class AMethodTheSiblingsWouldOverfillIsWrittenWithoutThemTest {

    private static final int FORKS = 4;

    private static final int TERMS = 450;

    private static String model() {
        StringBuilder body = new StringBuilder();
        StringBuilder sum = new StringBuilder();
        for (int f = 0; f < FORKS; f++) {
            StringBuilder held = new StringBuilder();
            StringBuilder other = new StringBuilder();
            for (int t = 1; t <= TERMS; t++) {
                held.append(t == 1 ? "" : ", ").append("x * ").append(t);
                other.append(t == 1 ? "" : ", ").append("x * ").append(t + 1000);
            }
            body.append("    let a").append(f).append(" = if x > ").append(f)
                    .append(" then List.sum([").append(held).append("]) else List.sum([")
                    .append(other).append("])\n");
            sum.append(f == 0 ? "" : " + ").append("a").append(f);
        }
        // At nought every fork takes its second arm and every term is nought; at nine every fork
        // takes its first, and each sums nine times one to four hundred and fifty.
        long atNine = (long) FORKS * 9 * TERMS * (TERMS + 1) / 2;
        return """
                module example.wide

                behavior f : (x: Int) -> Int

                let f (x) = {
                %s
                    %s
                }

                example f
                    | (0) -> 0
                    | (9) -> %d
                """.formatted(body, sum, atNine);
    }

    @Test
    void aMeasuredBuildOfABodyTheJvmHoldsCompiles() {
        Compilation compilation = Compilation.ofSource(model(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

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
        Compilation compilation = Compilation.ofSource(model(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, ReplacementEvidence> measured = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().getFirst())).value();

        List<ReplacementEvidence.Rewrite> rewrites = measured.get("f").measured().made()
                .orElseThrow(() -> new AssertionError("the rewrites were measured: " + measured))
                .rewrites();
        assertTrue(rewrites.stream().anyMatch(each -> each.outcome()
                        instanceof ReplacementEvidence.Undecided(var why)
                        && why.contains(ReplacementEvidence.Undecided.Why.TOO_LARGE)),
                () -> "a rewrite the method had no room for: " + rewrites);
    }
}
