package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Place;

/**
 * What a search is asked at one of a row's numbers.
 *
 * <p><b>Three answers and not one set.</b> What an account walks, which number a caller has already
 * picked to try, and what a walk that came back empty-handed is entitled to say are three
 * questions. A set of one number answers all three the same way — walk this number, try this
 * number, there was no other — and two of those are true of a caller that picked a number out of a
 * class while the third is not.
 *
 * <p>So {@link #about} is the subject of whatever is concluded and {@link #walked} is how the
 * looking was done. A class of a row is its own subject and the walk of it is the walk of the
 * question; a number a point is tried with is a candidate out of a wider question, and a walk that
 * ran out of it ran out of a candidate.
 *
 * @param about  the numbers this is a search about, which is what a word said of it is said of
 * @param walked the numbers the account is to write values at, and how they stand to the ones above
 */
public record AskedAt(NumbersAskedFor about, Walked walked) {

    public AskedAt {
        if (about == null || walked == null) {
            throw new IllegalArgumentException(
                    "a search is about some numbers and walks some: " + about + " " + walked);
        }
    }

    /**
     * The numbers an account is to walk, and what walking them comes to.
     *
     * <p><b>Said where the search is built and never worked out afterwards.</b> Whether walking
     * these is walking what the search is about is a fact about two sets, and every other fact
     * here only correlates with it: that nobody picked a number holds of a class walked whole and
     * of a set whose question nothing could state alike. Read off one of those, a walk of part of
     * something comes back as a walk of all of it the day a builder has to answer with a question
     * it did not have.
     *
     * <p>Closed, so a way of looking that is added says what a walk of it shows rather than
     * falling to whichever arm was nearest.
     */
    public sealed interface Walked {

        /** The numbers to walk. */
        NumericSet numbers();

        /** The number a caller picked to try, or null where none did. */
        Place named();

        /**
         * Every number the search is about, so walking them is walking the question.
         *
         * <p>Which is what a class of a row is asked for: what the rules leave is the subject and
         * the account chooses among it.
         */
        record AllOfIt(NumericSet numbers) implements Walked {

            @Override
            public Place named() {
                return null;
            }
        }

        /**
         * One number a caller picked out of what the search is about.
         *
         * <p>Its failing says nothing about the numbers beside it, unless the search is about that
         * number and no other — which the question answers and this does not.
         */
        record OneOfThem(NumericSet numbers, Place named) implements Walked {}

        /**
         * Numbers to try where nothing could say what question they are numbers of.
         *
         * <p>A set on an order this reading does not have. What the rules leave it cannot be read,
         * so there is nothing for a walk of these to have covered and nothing a walk of them shows
         * — which is not the same as a walk that covered a question holding everything.
         */
        record SomeOfSomethingUnsaid(NumericSet numbers, Place named) implements Walked {}
    }

    /** The numbers the account is to write values at. */
    public NumericSet walking() {
        return walked.numbers();
    }

    /** The number a caller picked to try, or null where it picked none. */
    public Place named() {
        return walked.named();
    }

    /**
     * Whether walking {@link #walking()} to the end is walking what this is about.
     *
     * <p><b>What a walk that reached no value may be said to have shown.</b> False here and the
     * walk showed nothing about the model however far it ran, which is why it is answered by what
     * was walked and what it was about rather than by how the search went.
     */
    public boolean walkIsOfTheWholeQuestion() {
        return switch (walked) {
            case Walked.AllOfIt _ -> true;
            // The one number, where the question is that number: a search asked for one number
            // that tries it has tried every number there is of it.
            case Walked.OneOfThem _ -> about.isOneNumber();
            case Walked.SomeOfSomethingUnsaid _ -> false;
        };
    }

    /**
     * A class of the row, which a search of is a search about.
     *
     * <p>No candidate, because nothing picked one: what a class asks for is a value of the class,
     * and which of its numbers that value stands at is the account's to choose.
     */
    public static AskedAt theClass(NumericSet admitted, Carrier on) {
        return aNumberOutOf(admitted, null, on);
    }

    /**
     * A class of the row, with one of its numbers a caller has already paid to name.
     *
     * <p>The class is still the subject: which of its numbers this tries first says nothing about
     * the ones beside it.
     *
     * <p>Where there is no order to read the class on, what the rules leave cannot be read either
     * — so what is walked is some of something unsaid, and a walk of it shows nothing whether or
     * not a caller named one of them.
     */
    public static AskedAt aNumberOutOf(NumericSet admitted, Place named, Carrier on) {
        if (on == null) {
            return new AskedAt(NumbersAskedFor.ANYTHING,
                    new Walked.SomeOfSomethingUnsaid(admitted, named));
        }
        return new AskedAt(NumbersAskedFor.ofTheClass(admitted, on),
                named == null ? new Walked.AllOfIt(admitted)
                        : new Walked.OneOfThem(admitted, named));
    }

    /**
     * One number a caller picked, out of what it was asking about.
     *
     * <p>The number is what gets walked — this is where a point search says which value it is
     * trying, and trying another is the caller's to ask for. What it is a number <em>of</em> is
     * carried beside it, so that running out of this one is not running out of them.
     */
    public static AskedAt oneNumberOf(NumbersAskedFor about, Place named) {
        return new AskedAt(about, new Walked.OneOfThem(new NumericSet.At(named), named));
    }
}
