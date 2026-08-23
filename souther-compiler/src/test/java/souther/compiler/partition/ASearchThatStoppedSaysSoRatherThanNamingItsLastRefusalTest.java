package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a class comes to when the search for it ran out of room.
 *
 * <p>A class is looked for against every value the model states, each walked outward from the
 * target alone, and the walk is bounded. The bound is a fact about the search: past it there are
 * assignments nothing tried, and one of them may be the one that builds. Read off the end of the
 * list of what was tried, the two came out the same — a walk that ran out of assignments and one
 * that ran out of budget both end, and the last refusal was offered as the class's answer either
 * way.
 *
 * <p>Which is a claim about the model made on the strength of a limit. "Every value tried was
 * refused" over a search that stopped one short of the value that builds sends a reader looking for
 * a rule to change; what they have is a search to widen.
 */
class ASearchThatStoppedSaysSoRatherThanNamingItsLastRefusalTest {

    /**
     * A rule relating two fields, and more values of the type than the walk has room for.
     *
     * <p>Every one of them holds {@code lo} above the class {@code hi} is looked for in, so the
     * target moved alone is refused at each — and the repair that works, moving {@code lo} beside
     * it, sits one distance further out. The values are alike on purpose: what is being asked is
     * what the search says when it stops, and a value that built would end the walk before it.
     */
    private static String crowded() {
        StringBuilder lets = new StringBuilder();
        for (int i = 0; i <= 64; i++) {
            lets.append("let m").append(i)
                    .append(" = Request { lo = Amount(60), hi = Amount(7").append(i % 10)
                    .append(") }\n\n");
        }
        return """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Request = { lo: Amount, hi: Amount }
                    invariant lo.value <= hi.value

                data Accepted = { at: String }

                %s
                behavior submit : (request: Request) -> Accepted
                    constructs Accepted

                let submit (request) = {
                    guard request.lo.value <= 50 else Accepted { at = "wide" }
                    guard request.hi.value <= 60 else Accepted { at = "tall" }
                    Accepted { at = "now" }
                }
                """.formatted(lets.toString());
    }

    /**
     * The class the walk did not reach the repair for says the search stopped.
     *
     * <p>{@code hi} at the bottom of its lower class is under every stated {@code lo}, which the
     * rule refuses, so each of the sixty-five values fails at the target alone. The repair — moving
     * {@code lo} down beside it — is a distance further out and the budget is spent before the walk
     * gets there, and so is the composition from the classes that sits behind them all.
     */
    @Test
    void aClassTheBudgetStoppedShortOfSaysTheSearchStopped() {
        Adequacy.Filling filling = generated(crowded()).get("submit");
        assertNotNull(filling, "the behavior under test is generated for");

        Generator.ClassAttempt at = attemptAtTheLowerHi(filling);
        assertEquals(Generator.UnresolvedCombination.Reason.SEARCH_LIMIT,
                ((Generator.ClassAttempt.Unresolved) at).why().reason(),
                "the search stopped, and what the last value it got to came to is that value's "
                        + "news and not the class's: " + at);
    }

    /** What the search made of the class {@code hi} takes below the line the body draws. */
    private static Generator.ClassAttempt attemptAtTheLowerHi(Adequacy.Filling filling) {
        for (Generator.ClassAttempt each : filling.composed().classes()) {
            if (each.at().term().endsWith("hi") && each.classId().contains("0")) {
                return each;
            }
        }
        throw new AssertionError("the lower class of `hi` is one the search was asked about: "
                + filling.composed().classes());
    }

    private static Map<String, Adequacy.Filling> generated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all;
    }
}
