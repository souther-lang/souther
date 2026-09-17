package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Place;

/**
 * What a search is asked at one of a row's numbers.
 *
 * <p><b>Three answers that used to be one set.</b> What an account walks, which number a caller
 * has already picked to try, and what a walk that came back empty-handed is entitled to say — those
 * were one {@link NumericSet}, and a set of one number said all three: walk this number, try this
 * number, and there was no other. Two of those are true of a caller that picked a number out of a
 * class, and the third is not.
 *
 * <p>So {@link #about} is the subject of whatever is concluded and the other two are how the
 * looking was done. A class of a row is its own subject and the walk of it is the walk of the
 * question; a number a point is tried with is a candidate out of a wider question, and a walk that
 * ran out of it ran out of a candidate.
 *
 * @param about   the numbers this is a search about, which is what a word said of it is said of
 * @param walking the numbers the account is to write values at, in the vocabulary an account walks
 * @param named   the number a caller picked to try, or null where it picked none
 */
public record AskedAt(NumbersAskedFor about, NumericSet walking, Place named) {

    public AskedAt {
        if (about == null || walking == null) {
            throw new IllegalArgumentException(
                    "a search is about some numbers and walks some: " + about + " " + walking);
        }
    }

    /**
     * Whether walking {@link #walking} to the end is walking what this is about.
     *
     * <p>Where nothing picked a number, the numbers to walk are the ones this is about and walking
     * them is walking the question. Where something did, they are the one it picked — so only a
     * question of one number is walked by trying it, and every wider one has numbers beside it that
     * nothing looked at.
     *
     * <p><b>What a walk that reached no value may be said to have shown.</b> False here and the
     * walk showed nothing about the model however far it ran, which is why this is asked of what
     * was being searched for rather than of how the search went.
     */
    public boolean walkIsOfTheWholeQuestion() {
        return named == null || about.isOneNumber();
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
     * the ones beside it. Where there is no order to read the class on, nothing is known of the
     * numbers it holds — so the question is every number there is, which is the answer that lets
     * nothing be concluded from a walk of it.
     */
    public static AskedAt aNumberOutOf(NumericSet admitted, Place named, Carrier on) {
        return new AskedAt(on == null ? NumbersAskedFor.ANYTHING
                : NumbersAskedFor.ofTheClass(admitted, on), admitted, named);
    }

    /**
     * One number a caller picked, out of what it was asking about.
     *
     * <p>The number is what gets walked — this is where a point search says which value it is
     * trying, and trying another is the caller's to ask for. What it is a number <em>of</em> is
     * carried beside it, so that running out of this one is not running out of them.
     */
    public static AskedAt oneNumberOf(NumbersAskedFor about, Place named) {
        return new AskedAt(about, new NumericSet.At(named), named);
    }
}
