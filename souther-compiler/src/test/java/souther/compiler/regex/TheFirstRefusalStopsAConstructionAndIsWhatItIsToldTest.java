package souther.compiler.regex;

import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A construction stops where it is first refused, and that refusal is what it is told about.
 *
 * <p>Two things and not one. Nothing more is built after a step comes back with nothing — the states
 * would be made for an operation that is never going to happen, out of the same allowance the rest
 * of the answer draws on. And what stopped it is the first limit that said no, whatever else happens
 * to a meter that outlives the build.
 *
 * <p>They are kept apart because they fail apart. A builder that forgets to stop makes work nobody
 * needed, and it also puts its own limit where the reason goes — so a rule an author could rewrite
 * is reported as an allowance that ran out, or the other way round. The second is the one that
 * reaches a person.
 */
class TheFirstRefusalStopsAConstructionAndIsWhatItIsToldTest {

    private static PatternMeaning read(String regex) {
        return assertInstanceOf(PatternRead.Read.class, PatternParser.read(regex), regex).meaning();
    }

    private static PatternPlan of(String regex) {
        return PatternPlan.of(read(regex));
    }

    /**
     * A meet whose left side is larger than a machine may be, and whose right side would fit.
     *
     * <p>The left is refused for being one machine too large. Built on, the right takes states out
     * of what is left — and where that runs out too, the meter's last word is about the allowance
     * and not about the pattern somebody wrote.
     */
    @Test
    void nothingIsBuiltAfterAStepIsRefusedAndTheReasonIsTheFirstOne() {
        // Room for the left side to be refused for being one machine too large — it spends four
        // hundred getting there — and less than the right side needs left over afterwards.
        Meter meter = new Meter(400, 600, 1_000_000_000L);
        PatternPlan plan = of("a{500}").and(of("b{300}"));

        assertNull(plan.compile(meter), "the left side does not fit, so the meet is not built");
        assertEquals(Meter.Stopped.ONE_MACHINE, meter.stoppedBy(),
                "and what stopped it is the side that is larger than a machine may be");
        assertEquals(200, meter.left(),
                "the right side was never built, so what it would have cost is still there");
    }

    /** And a build that comes back with nothing is not told what refused an earlier one. */
    @Test
    void whatRefusedAnEarlierConstructionIsNotThisOnesReason() {
        Meter meter = new Meter(400, 100_000, 1_000_000_000L);
        assertNull(of("a{500}").compile(meter), "larger than a machine may be");
        assertEquals(Meter.Stopped.ONE_MACHINE, meter.stoppedBy());

        // And now a small one, out of what the refused build left behind.
        assertNotNull(of("a{5}").compile(meter), "a small one is built out of what is left");
        assertNull(meter.stoppedBy(), "so nothing refused it, whatever refused the one before");
    }
}
