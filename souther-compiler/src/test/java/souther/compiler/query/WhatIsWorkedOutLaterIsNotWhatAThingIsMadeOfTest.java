package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.CompoundSamples;
import souther.compiler.meaning.Proposition;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A {@code volatile} field is an answer worked out later from the rest of a thing, and neither walk
 * reads it as part of what the thing is made of ({@link AnswerShape#madeOf}).
 *
 * <p>Each assertion beside its control: the same shape with the field written as an ordinary one,
 * which both walks read, so a walk that stopped reading fields at all would fail the control.
 */
class WhatIsWorkedOutLaterIsNotWhatAThingIsMadeOfTest {

    /** Something that says which object it is and nothing else, which is what a walk looks for. */
    private static final class Address {}

    /** Something worked out later and kept beside what it is worked out from. */
    private static final class Later {

        private volatile Address workedOut;

        @Override
        public boolean equals(Object other) {
            return other instanceof Later;
        }

        @Override
        public int hashCode() {
            return 0;
        }
    }

    /** The same, written as an ordinary field. */
    private static final class Now {

        private Address held;

        @Override
        public boolean equals(Object other) {
            return other instanceof Now;
        }

        @Override
        public int hashCode() {
            return 0;
        }
    }

    private record KeepingLater(String name, Later later) {}

    private record KeepingNow(String name, Now now) {}

    private static Later workedOut() {
        Later later = new Later();
        later.workedOut = new Address();
        return later;
    }

    private static Now held() {
        Now now = new Now();
        now.held = new Address();
        return now;
    }

    private static Set<String> found(AnswerWalk.Walked walked) {
        Set<String> out = new TreeSet<>();
        List<AnswerWalk.Found> all = switch (walked.covered()) {
            case Covered.Whole<AnswerWalk.Found>(List<AnswerWalk.Found> each) -> each;
            case Covered.Partly<AnswerWalk.Found>(List<AnswerWalk.Found> each, List<Gap> _) -> each;
        };
        all.forEach(each -> out.add(each.place().asText()));
        return out;
    }

    private static Set<String> gaps(AnswerWalk.Walked walked) {
        Set<String> out = new TreeSet<>();
        if (walked.covered() instanceof Covered.Partly<AnswerWalk.Found>(
                List<AnswerWalk.Found> _, List<Gap> gaps)) {
            gaps.forEach(each -> out.add(each.toString()));
        }
        return out;
    }

    private static Set<String> found(Covered<Divergence> covered) {
        List<Divergence> each = switch (covered) {
            case Covered.Whole<Divergence>(List<Divergence> all) -> all;
            case Covered.Partly<Divergence>(List<Divergence> all, List<Gap> _) -> all;
        };
        Set<String> out = new LinkedHashSet<>();
        each.forEach(one -> out.add(one.at().asText() + " " + one.cause() + " " + one.kind()));
        return out;
    }

    @Test
    void theWalkOfOneThingDoesNotGoIntoWhatIsWorkedOutLater() {
        assertEquals(Set.of(), found(AnswerWalk.of("Q", new KeepingLater("a", workedOut()))));
        assertEquals(Set.of("Q.KeepingNow#now.Now#held " + Address.class.getName()),
                found(AnswerWalk.of("Q", new KeepingNow("a", held()))), "the control");
    }

    /** Two things alike in the rest are one thing whichever of them worked out what it keeps. */
    @Test
    void thePairWalkDoesNotCompareWhatIsWorkedOutLater() {
        assertEquals(Set.of(), found(Divergence.between(new KeepingLater("a", workedOut()),
                new KeepingLater("a", new Later()))));
        assertFalse(found(Divergence.between(new KeepingNow("a", held()),
                new KeepingNow("a", new Now()))).isEmpty(), "the control");
    }

    private record Counted(int count, boolean complete) {}

    /** What is primitive is still compared: it is what a thing is made of, and only the walk of
     *  one thing leaves it out, the language having said what it means. */
    @Test
    void thePairWalkStillComparesWhatIsPrimitive() {
        Set<String> found = found(Divergence.between(new Counted(1, true), new Counted(2, true)));

        assertFalse(found.isEmpty(), "two counts apart are two answers");
        assertEquals(Set.of(), found(Divergence.between(new Counted(1, true),
                new Counted(1, true))), "and two alike are one");
    }

    /**
     * A statement whose denial it keeps, and whose denial keeps it in turn, is walked as one that
     * kept nothing: not round the two of them, and with nothing found that the other is not found
     * with.
     */
    @Test
    void aStatementKeepingItsDenialIsWalkedAsOneThatKeepsNone() {
        Proposition keeping = Proposition.all(List.of(CompoundSamples.truth("walked.a"),
                CompoundSamples.numberAtLeastZero("walked.n")));
        keeping.denied().denied();
        Proposition.All all = (Proposition.All) keeping;
        Proposition keepingNone = new Proposition.All(all.parts());

        AnswerWalk.Walked walked = AnswerWalk.of("Q", keeping);
        AnswerWalk.Walked control = AnswerWalk.of("Q", keepingNone);
        assertEquals(found(control), found(walked));
        assertEquals(gaps(control), gaps(walked));
        assertEquals(Set.of(), found(Divergence.between(keeping, keepingNone)));

        AnswerWalk.Walked denial = AnswerWalk.of("Q", keeping.denied());
        AnswerWalk.Walked denialMadeAgain = AnswerWalk.of("Q", keepingNone.denied());
        assertEquals(found(denialMadeAgain), found(denial), "the denial walked on its own");
        assertEquals(gaps(denialMadeAgain), gaps(denial));
    }
}
