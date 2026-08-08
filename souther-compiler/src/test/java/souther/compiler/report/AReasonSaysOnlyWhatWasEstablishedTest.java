package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sentence about a reason is a claim about every place that writes it.
 *
 * <p>Turning the codes into sentences is how the report stops handing a reader an enum's name. It
 * is also how a reader gets told what happened on the authority of a name that may be wider than
 * the sentence — which is the defect this whole change is about, made once more one level up. So a
 * code is written out in words only where its producers have been read.
 */
class AReasonSaysOnlyWhatWasEstablishedTest {

    @Test
    void aSourceWithNoObservationSaysThatAndNotWhyItHadNone() {
        String said = Reasons.said(Incompleteness.of(Incompleteness.Code.OBSERVATION_ABSENT,
                Incompleteness.Scope.SOURCE, "1"));

        assertEquals("no rows were read from `1`, so what they cover is unknown", said);
    }

    /** Named for the error that was caught, and it says no more than that. The runtime being off
     * the classpath is the case it was written for and not the only one the JVM raises it for. */
    @Test
    void aLinkageFailureDoesNotClaimTheRuntimeIsMissing() {
        String said = Reasons.said(Incompleteness.of(Incompleteness.Code.LINKAGE_FAILED,
                Incompleteness.Scope.BEHAVIOR, "submit"));

        assertFalse(said.contains("runtime"), said);
        assertTrue(said.contains("would not link"), said);
    }

    /**
     * And it says what did not happen next, now that one producer is left to say it.
     *
     * <p>Three places wrote it: an example whose classes would not load, a fill that could not put
     * its candidates through the decoder, and a boundary that could not build one. Only the first
     * was rows that did not run — the other two happen after the rows were read — so the sentence
     * stopped where the three stopped agreeing. The other two are the generator's now and report in
     * its vocabulary, which leaves the example, where nothing was observed.
     *
     * <p>This holds the wording and not the producers. Which places write a code is not something a
     * unit of this size can walk; it is read by hand, and the reading is what the sentence rests
     * on — so it is re-read whenever a producer is added or taken away, as one was here.
     */
    @Test
    void aLinkageFailureSaysWhatItsOneProducerEstablishes() {
        String said = Reasons.said(Incompleteness.of(Incompleteness.Code.LINKAGE_FAILED,
                Incompleteness.Scope.BEHAVIOR, "submit"));

        assertEquals("the classes for `submit` would not link, so its rows did not run", said);
    }

    /**
     * A code with one producer says what that producer establishes, and that can be more than the
     * code alone.
     *
     * <p>{@code INSTRUMENTATION_ABSENT} is written at one place, on a branch taken only where arm
     * coverage was asked for, and it returns no rows with it. Both are part of what the sentence may
     * say. What it may not say is which of the things that stop those classes being made happened —
     * a backend that failed, inputs that were not there — because nothing there can tell them apart.
     */
    @Test
    void oneProducerLetsTheSentenceSayWhatThatProducerEstablishes() {
        String said = Reasons.said(Incompleteness.of(Incompleteness.Code.INSTRUMENTATION_ABSENT,
                Incompleteness.Scope.MODULE, "example.trip"));

        assertEquals("the classes `example.trip` needed for arm coverage could not be made,"
                + " so none of its rows were read", said);
    }

    /**
     * Every code says something now, and none of them says its own name back.
     *
     * <p>A reason reading {@code submit (value_unreadable)} is the data printed as though it were a
     * sentence: it tells a reader what the code was and nothing about what happened. Every code left
     * here is one a report is written in, and one whose producers have been read far enough to say
     * so in words.
     */
    @Test
    void noCodeIsPrintedAsItsOwnName() {
        for (Incompleteness.Code code : Incompleteness.Code.values()) {
            String said = Reasons.said(Incompleteness.of(code,
                    Incompleteness.Scope.BEHAVIOR, "submit"));

            assertNotEquals("submit (" + code.name().toLowerCase(java.util.Locale.ROOT) + ")", said,
                    code + " is printed as itself");
            assertTrue(said.contains("submit"), code + " does not say what it is about: " + said);
        }
    }
}
