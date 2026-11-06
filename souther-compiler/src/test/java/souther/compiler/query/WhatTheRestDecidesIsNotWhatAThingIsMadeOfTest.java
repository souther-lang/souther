package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.identity.DecidedByTheRest;
import souther.compiler.meaning.CompoundSamples;
import souther.compiler.meaning.Proposition;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field that says the rest decides it ({@link DecidedByTheRest}) is not what a thing is made of
 * to either walk of an answer ({@link AnswerShape#madeOf}), and a walk says it passed over it.
 *
 * <p>Each assertion beside its control: the same shape with the field left unmarked, which both
 * walks read, so a walk that stopped reading fields at all would fail the control. And a field
 * that is only {@code volatile} is read like any other, since that says how it is seen across
 * threads and nothing about what it means.
 */
class WhatTheRestDecidesIsNotWhatAThingIsMadeOfTest {

    /** Something that says which object it is and nothing else, which is what a walk looks for. */
    private static final class Address {}

    /** Something kept beside what decides it, which compares as nothing of its own. */
    private record Kept(Address held) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Kept;
        }

        @Override
        public int hashCode() {
            return 0;
        }
    }

    private record KeepingDecided(String name, @DecidedByTheRest Kept kept) {}

    private record KeepingPlain(String name, Kept kept) {}

    /** What a worker hands over across threads: {@code volatile}, and what the thing is. */
    private static final class HeldAcrossThreads {

        private volatile int state;
        private volatile Address handedOver;

        HeldAcrossThreads(int state, Address handedOver) {
            this.state = state;
            this.handedOver = handedOver;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof HeldAcrossThreads that && state == that.state
                    && handedOver == that.handedOver;
        }

        @Override
        public int hashCode() {
            return Integer.hashCode(state);
        }
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
    void theWalkOfOneThingPassesOverWhatTheRestDecidesAndSaysSo() {
        AnswerWalk.Walked walked =
                AnswerWalk.of("Q", new KeepingDecided("a", new Kept(new Address())));

        assertEquals(Set.of(), found(walked));
        assertEquals(Set.of(KeepingDecided.class.getName() + "#kept"), walked.passedOver());

        AnswerWalk.Walked control =
                AnswerWalk.of("Q", new KeepingPlain("a", new Kept(new Address())));
        assertEquals(Set.of("Q.KeepingPlain#kept.Kept#held " + Address.class.getName()),
                found(control), "the control");
        assertEquals(Set.of(), control.passedOver(), "the control");
    }

    /** Two things alike in the rest are one thing whatever the field the rest decides holds. */
    @Test
    void thePairWalkDoesNotCompareWhatTheRestDecides() {
        assertEquals(Set.of(), found(Divergence.between(
                new KeepingDecided("a", new Kept(new Address())),
                new KeepingDecided("a", new Kept(null)))));
        assertFalse(found(Divergence.between(new KeepingPlain("a", new Kept(new Address())),
                new KeepingPlain("a", new Kept(null)))).isEmpty(), "the control");
    }

    /** A field that is {@code volatile} and nothing more is what the thing is: compared by the
     *  pair walk, primitive or not, and gone into by the walk of one. */
    @Test
    void aVolatileFieldIsWhatAThingIsMadeOf() {
        Address one = new Address();
        assertTrue(found(Divergence.between(new HeldAcrossThreads(1, one),
                        new HeldAcrossThreads(2, one))).stream()
                        .anyMatch(each -> each.endsWith(Divergence.Kind.DIFFERENT_THINGS.name())),
                "two states apart are two answers");
        assertEquals(Set.of(), found(Divergence.between(new HeldAcrossThreads(1, one),
                new HeldAcrossThreads(1, one))), "and two alike are one");

        AnswerWalk.Walked walked = AnswerWalk.of("Q", new HeldAcrossThreads(1, new Address()));
        assertEquals(Set.of("Q.HeldAcrossThreads#handedOver " + Address.class.getName()),
                found(walked));
        assertEquals(Set.of(), walked.passedOver());
    }

    private record Counted(int count, boolean complete) {}

    /** What is primitive is still compared: it is what a thing is made of, and only the walk of
     *  one thing leaves it out, the language having said what it means. */
    @Test
    void thePairWalkStillComparesWhatIsPrimitive() {
        assertFalse(found(Divergence.between(new Counted(1, true), new Counted(2, true)))
                .isEmpty(), "two counts apart are two answers");
        assertEquals(Set.of(), found(Divergence.between(new Counted(1, true),
                new Counted(1, true))), "and two alike are one");
    }

    /**
     * A statement whose denial it keeps, and whose denial keeps it in turn, is walked as one that
     * kept nothing: not round the two of them, with nothing found that the other is not found with,
     * and the cell said to be passed over. Its denial walked on its own is walked whole.
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
        assertTrue(walked.passedOver().contains(Proposition.All.class.getName() + "#denial"),
                walked.passedOver().toString());
        assertEquals(Set.of(), found(Divergence.between(keeping, keepingNone)));

        Proposition.Any denied = (Proposition.Any) keeping.denied();
        AnswerWalk.Walked denial = AnswerWalk.of("Q", denied);
        AnswerWalk.Walked madeApart = AnswerWalk.of("Q", new Proposition.Any(denied.parts()));
        assertEquals(found(madeApart), found(denial), "the denial walked on its own");
        assertEquals(gaps(madeApart), gaps(denial));
        assertEquals(Set.of(), gaps(denial));
    }
}
