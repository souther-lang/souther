package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The walk of what a question declares, held to its rules by declarations written for it.
 *
 * <p>Everything else asked of this walk is asked over the questions this compiler happens to
 * declare, and what that shows moves with what the compiler is. These are the rules themselves: a
 * shape is written here, walked, and what comes back is what the rule says. A rule that stops being
 * kept fails here whatever the compiler has come to look like.
 *
 * <p>Written as questions because that is what the walk takes. Nothing asks them and nothing counts
 * them among what this compiler declares — {@link DeclaredQuestions} reads the classes the compiler
 * was compiled to, and these are not among them.
 */
class AWalkOfWhatIsDeclaredStopsWhereNothingSettlesItTest {

    /** Something that says what it is and can still be extended. */
    private static class OpenToAnything {

        private final String said;

        OpenToAnything(String said) {
            this.said = said;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof OpenToAnything that && said.equals(that.said);
        }

        @Override
        public int hashCode() {
            return said.hashCode();
        }
    }

    /** Something written with what it holds, whose own equality is an address. */
    private record ADequeIsAnswered() implements Key<ArrayDeque<String>> {

        @Override
        public Answer<ArrayDeque<String>> compute(Db db) {
            return Answer.absent();
        }
    }

    private record AnOpenTypeIsAnswered() implements Key<OpenToAnything> {

        @Override
        public Answer<OpenToAnything> compute(Db db) {
            return Answer.absent();
        }
    }

    /** Something to find, one step under something that has to be walked into to find it. */
    private record Holding(ArrayDeque<String> bad) {}

    private record TwoWaysToOneThing(Holding one, Holding two) {}

    private record TwoWaysAreAnswered() implements Key<TwoWaysToOneThing> {

        @Override
        public Answer<TwoWaysToOneThing> compute(Db db) {
            return Answer.absent();
        }
    }

    /** A declaration that reaches itself, with something to find under it. */
    private record ItselfAgain(Optional<ItselfAgain> next, ArrayDeque<String> held) {}

    private record ItselfAgainIsAnswered() implements Key<ItselfAgain> {

        @Override
        public Answer<ItselfAgain> compute(Db db) {
            return Answer.absent();
        }
    }

    private record Boxed<T>(T held) {}

    private record TwoBoxes(Boxed<ArrayDeque<String>> bad, Boxed<String> good) {}

    private record TwoBoxesAreAnswered() implements Key<TwoBoxes> {

        @Override
        public Answer<TwoBoxes> compute(Db db) {
            return Answer.absent();
        }
    }

    /** What the walk came to, as what it stopped on and where, in the order it went. */
    private static List<String> walking(Class<?> question) {
        return DeclaredAnswerWalk.of(List.of(question)).found().stream()
                .map(each -> each.why() + " at " + each.place().at().asText()
                        + " " + each.place().offender())
                .toList();
    }

    /**
     * A container is asked what it is before it is read for what it holds.
     *
     * <p>Which is the whole of what one walk had wrong: read for what it holds first, a thing whose
     * own equality is an address comes back clean because everything inside it is a string.
     */
    @Test
    void aContainerThatSaysNothingOfItselfIsNotReadForWhatItHolds() {
        assertEquals(List.of("SAYS_NOTHING_OF_ITSELF at  java.util.ArrayDeque"),
                walking(ADequeIsAnswered.class));
    }

    /** And a type anything may extend is where the declarations run out, whatever it says. */
    @Test
    void aTypeNothingClosesIsWhereTheDeclarationsStop() {
        assertEquals(List.of("NOTHING_CLOSES_IT at "
                        + " souther.compiler.query."
                        + "AWalkOfWhatIsDeclaredStopsWhereNothingSettlesItTest$OpenToAnything"),
                walking(AnOpenTypeIsAnswered.class));
    }

    /**
     * What is found under a thing is said at every path that reaches the thing.
     *
     * <p>Written down once, a register would hold whichever way down the walk happened to take
     * first, and the other would be a place nobody had looked at.
     *
     * <p>Under something the walk has to go into, so that the second way down is answered from what
     * was found under the first rather than found again from the top. Held directly, the two would
     * be two things the walk stopped at and would say nothing about what it remembers.
     */
    @Test
    void whatIsFoundUnderAThingIsSaidAtEveryPathThatReachesIt() {
        assertEquals(List.of(
                        "SAYS_NOTHING_OF_ITSELF at .TwoWaysToOneThing#one.Holding#bad"
                                + " java.util.ArrayDeque",
                        "SAYS_NOTHING_OF_ITSELF at .TwoWaysToOneThing#two.Holding#bad"
                                + " java.util.ArrayDeque"),
                walking(TwoWaysAreAnswered.class));
    }

    /**
     * A declaration that reaches itself is walked once and is not a defect.
     *
     * <p>A shape that holds another of its own kind is a shape. What is under it is asked about
     * where it was first met, and following it again is the same question one step further down
     * forever.
     */
    @Test
    void aDeclarationThatReachesItselfEnds() {
        assertEquals(List.of("SAYS_NOTHING_OF_ITSELF at .ItselfAgain#held java.util.ArrayDeque"),
                walking(ItselfAgainIsAnswered.class));
    }

    /**
     * One declaration under two sets of arguments is two shapes.
     *
     * <p>What it holds is what the arguments say it holds, so a walk that remembered it by the
     * declaration alone would come back from the second saying what it found in the first.
     */
    @Test
    void aDeclarationIsReadAgainUnderOtherArguments() {
        assertEquals(List.of(
                        "SAYS_NOTHING_OF_ITSELF at .TwoBoxes#bad.Boxed#held java.util.ArrayDeque"),
                walking(TwoBoxesAreAnswered.class));
    }
}
