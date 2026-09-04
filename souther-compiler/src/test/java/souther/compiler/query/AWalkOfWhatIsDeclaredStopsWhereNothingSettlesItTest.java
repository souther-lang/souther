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

    /** Something of one's own that is a number the way its author says it is. */
    private static final class ANumberOfItsOwn extends Number {

        /** What extending a number brings with it, and what nothing here is about. */
        private static final long serialVersionUID = 1L;

        @Override
        public int intValue() {
            return 0;
        }

        @Override
        public long longValue() {
            return 0;
        }

        @Override
        public float floatValue() {
            return 0;
        }

        @Override
        public double doubleValue() {
            return 0;
        }
    }

    private record ANumberOfItsOwnIsAnswered() implements Key<ANumberOfItsOwn> {

        @Override
        public Answer<ANumberOfItsOwn> compute(Db db) {
            return Answer.absent();
        }
    }

    /** Something of one's own that is a map the way its author says it is. */
    private static final class AMapOfItsOwn extends java.util.AbstractMap<String, String> {

        /** What it answers with beside its entries, which is the whole reason it is not one of the
         *  language's own maps. Read by the walk and by nothing here. */
        @SuppressWarnings("UnusedVariable")
        private final ArrayDeque<String> beside = new ArrayDeque<>();

        @Override
        public java.util.Set<Entry<String, String>> entrySet() {
            return java.util.Set.of();
        }
    }

    private record AMapOfItsOwnIsAnswered() implements Key<AMapOfItsOwn> {

        @Override
        public Answer<AMapOfItsOwn> compute(Db db) {
            return Answer.absent();
        }
    }

    private record ACollectionIsAnswered() implements Key<java.util.Collection<String>> {

        @Override
        public Answer<java.util.Collection<String>> compute(Db db) {
            return Answer.absent();
        }
    }

    private record AListIsAnswered() implements Key<List<String>> {

        @Override
        public Answer<List<String>> compute(Db db) {
            return Answer.absent();
        }
    }

    private record AnIdentityMapIsAnswered()
            implements Key<java.util.IdentityHashMap<String, String>> {

        @Override
        public Answer<java.util.IdentityHashMap<String, String>> compute(Db db) {
            return Answer.absent();
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

    /**
     * What the language settles is a list of things and not whatever is under one of them.
     *
     * <p>Something that extends a number is a number the way its author says it is: it may hold a
     * value it can be told to change, and it may say only which object it is. Admitted for being a
     * number, it would go past every question this asks.
     */
    @Test
    void aNumberOfSomebodysOwnIsNotWhatTheLanguageSettles() {
        assertEquals(List.of("SAYS_NOTHING_OF_ITSELF at "
                        + " souther.compiler.query."
                        + "AWalkOfWhatIsDeclaredStopsWhereNothingSettlesItTest$ANumberOfItsOwn"),
                walking(ANumberOfItsOwnIsAnswered.class));
    }

    /**
     * Holding things is not the contract.
     *
     * <p>What the language says about comparing two collections is that it says nothing beyond
     * comparing two objects: a thing that implements no more than a collection may answer by which
     * object it is and be within its rights. So a declaration that writes one has settled that it
     * holds strings and nothing about what comparing two of them compares — which is where the
     * declarations stop, whatever is under it.
     *
     * <p>Beside the one below, which is the same declaration written one step down and is read for
     * what it holds. Between them they say the rule is what each type's own specification says
     * about comparing two, and not what a type is under.
     */
    @Test
    void aCollectionIsNotAContractAboutComparingTwoOfThem() {
        assertEquals(List.of("NOTHING_CLOSES_IT at  java.util.Collection"),
                walking(ACollectionIsAnswered.class));
    }

    /** And a list, which says what comparing two of them compares, is read for what it holds. */
    @Test
    void aListIsReadForWhatItHolds() {
        assertEquals(List.of(), walking(AListIsAnswered.class));
    }

    /**
     * What a declaration writes is the contract or it is a thing of its own.
     *
     * <p>Naming an implementation names what that implementation does. The language ships one whose
     * equality is which objects were put in it, and read for what it holds — because it is a map,
     * and a map's equality is its entries — two of them holding equal things would be one where
     * they are two. So a declaration naming it is read as naming that class, which nothing closes.
     */
    @Test
    void aMapTheLanguageShipsThatKeepsNoneOfTheContractIsNotReadForWhatItHolds() {
        assertEquals(List.of("NOTHING_CLOSES_IT at  java.util.IdentityHashMap"),
                walking(AnIdentityMapIsAnswered.class));
    }

    /**
     * And a map of somebody's own is read for everything it holds.
     *
     * <p>What makes reading a map its entries enough is that the map is all there is of it. One of
     * this compiler's own holds whatever else it was written to hold — and answers with it — so
     * read as a map it would be read for the entries and never meet the rest.
     */
    @Test
    void aMapOfSomebodysOwnIsReadAsWhatItIs() {
        assertEquals(List.of("SAYS_NOTHING_OF_ITSELF at .AMapOfItsOwn#beside java.util.ArrayDeque",
                        // And what it keeps from the map it extends, which the language declares as
                        // a collection and says nothing about comparing two of.
                        "NOTHING_CLOSES_IT at .AbstractMap#values java.util.Collection"),
                walking(AMapOfItsOwnIsAnswered.class));
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
