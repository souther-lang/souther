package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Readings that share no position are held together rather than multiplied together.
 *
 * <p>A reading is a union of products, so a conjunction of two distributes. Where the two speak
 * about the same positions that is the answer and there is nothing cheaper to have. Where they share
 * nothing, no pair is ever dropped and every product is the two put side by side — the alternatives
 * multiply and say what the pair already said.
 *
 * <p>Which is what a behavior's input is made of: one reading per parameter, each over positions the
 * others do not name. Multiplied, ten parameters of a two-alternative record are a thousand and
 * twenty-four alternatives, and the budget that admitted each reading was counted per declaration.
 */
class ReadingsConjoinedAreNotMultipliedTest {

    /**
     * What puts the sets of these readings together.
     *
     * <p>One for the file, and one for every conjunction in it: a conjunction is the one place two
     * readings of a declaration come together, so the composer that paid for the sets in one is the
     * composer the next meet spends from. Every set here is values written out, so nothing is built
     * and no allowance is spent.
     */
    private static final Sets<String> SETS = Sets.ofAdmittedValues();

    /** Two readings over positions neither shares, each holding two alternatives. */
    @Test
    void readingsOverDisjointPositionsStayApart() {
        ConjoinedAdmissibleValues<String> both =
                ConjoinedAdmissibleValues.of(twoAlternatives("a", "b"), SETS)
                        .meet(ConjoinedAdmissibleValues.of(twoAlternatives("c", "d"), SETS));

        assertEquals(2, both.factors().size(), "one factor per reading");
        both.factors().forEach(each -> assertEquals(2, alternativesOf(each),
                "and each holds what it held"));
    }

    /** And the answers are the ones the product would have given. */
    @Test
    void andEachPositionIsAnsweredAsItWas() {
        ConjoinedAdmissibleValues<String> both =
                ConjoinedAdmissibleValues.of(twoAlternatives("a", "b"), SETS)
                        .meet(ConjoinedAdmissibleValues.of(twoAlternatives("c", "d"), SETS));

        assertEquals(twoAlternatives("a", "b").at("a"), both.at("a"));
        assertEquals(twoAlternatives("c", "d").at("d"), both.at("d"));
        assertFalse(both.isBottom());
    }

    /**
     * Merged over connected components and not over pairs.
     *
     * <p>{@code {a,b}} beside {@code {c}}, met with {@code {b,c}}: merging the first against the
     * third makes a factor over {@code {a,b,c}}, which now meets the second. Merged pairwise in one
     * pass, two factors would be left sharing {@code c}, and every answer that rests on the
     * vocabularies being disjoint would be read off a factor that is not the only one naming its
     * subject.
     */
    @Test
    void factorsReachingEachOtherThroughAThirdAreOneFactor() {
        ConjoinedAdmissibleValues<String> apart =
                ConjoinedAdmissibleValues.of(twoAlternatives("a", "b"), SETS)
                        .meet(ConjoinedAdmissibleValues.of(
                                AdmissibleValues.at("c", just("x")), SETS));
        assertEquals(2, apart.factors().size());

        ConjoinedAdmissibleValues<String> joined = apart.meet(ConjoinedAdmissibleValues.of(
                AdmissibleValues.at("b", just("y"))
                        .meet(AdmissibleValues.at("c", just("x")), SETS), SETS));

        assertEquals(1, joined.factors().size(), "all three reach each other");
        assertEquals(Set.of("a", "b", "c"), joined.subjects());
        assertEquals(just("y"), joined.at("b"));
        assertEquals(just("x"), joined.at("c"));
    }

    /** A factor holding nothing leaves the conjunction nothing, whatever the others admit. */
    @Test
    void oneFactorHoldingNothingIsTheWholeHoldingNothing() {
        ConjoinedAdmissibleValues<String> both =
                ConjoinedAdmissibleValues.of(twoAlternatives("a", "b"), SETS)
                        .meet(ConjoinedAdmissibleValues.of(
                                AdmissibleValues.at("c", just("x"))
                                        .meet(AdmissibleValues.at("c", just("y")), SETS), SETS));

        assertTrue(both.isBottom());
    }

    /**
     * The readings of a component are met in the order they arrived, not in the order they were
     * reached.
     *
     * <p>{@link AdmissibleValues#meet} does not answer the same either way. Every reason two
     * readings gave at one position is kept, and they are kept in the order the readings were met —
     * so which order that is decides the order an author is shown their own rules in, and it has to
     * be the order the readings arrived, since that is the order a conjunction holds them in.
     *
     * <p>Three readings met at once, in a shape where the two orders differ. Held apart are one over
     * {@code {a, b}} and one over {@code {x}}, which share nothing; met with them is one over
     * {@code {b, x}}, which reaches both. Walking out of the first, {@code b} leads to the bridge and
     * the bridge leads to the third — so the bridge is reached second and the third last, while the
     * order they arrived in is the other way round. Both of the last two say why {@code x} went
     * unread, and the order they are said in is the whole difference.
     */
    @Test
    void aComponentIsMetInTheOrderItsReadingsArrived() {
        AdmissibleValues<String> named = AdmissibleValues.at("a", just("x"))
                .meet(AdmissibleValues.at("b", just("y")), SETS);
        AdmissibleValues<String> arrivedSecond =
                AdmissibleValues.unreadable(Set.of("x"), UnreadReason.FORM_NOT_READ);
        AdmissibleValues<String> bridge =
                AdmissibleValues.unreadable(Set.of("b", "x"), UnreadReason.RELATES_TWO_POSITIONS);

        ConjoinedAdmissibleValues<String> apart = ConjoinedAdmissibleValues.of(named, SETS)
                .meet(ConjoinedAdmissibleValues.of(arrivedSecond, SETS));
        assertEquals(2, apart.factors().size(), "these two share nothing");

        ConjoinedAdmissibleValues<String> joined =
                apart.meet(ConjoinedAdmissibleValues.of(bridge, SETS));

        assertEquals(1, joined.factors().size(), "and the third reaches both of them");
        assertEquals(List.of(UnreadReason.FORM_NOT_READ, UnreadReason.RELATES_TWO_POSITIONS),
                joined.whyUnread("x"),
                "both readings say why, in the order they arrived");
    }

    /**
     * A reading says nothing about a subject it does not name.
     *
     * <p>Which is what makes the two answers above exact rather than approximate: a factor that does
     * not name a position admits every value at it, so leaving it out of the answer leaves out
     * nothing. Fixed here because the whole design rests on it — a reading that constrained a
     * subject outside its own vocabulary could not be conjoined without being expanded.
     */
    @Test
    void aReadingSaysNothingAboutASubjectItDoesNotName() {
        AdmissibleValues<String> read = twoAlternatives("a", "b");

        assertFalse(read.subjects().contains("elsewhere"));
        assertTrue(read.at("elsewhere").isAny(), "every value stands at a position nothing named");
        assertTrue(read.projectionExactAt("elsewhere"));
        assertEquals(List.of(), read.whyUnread("elsewhere"));

        assertTrue(ConjoinedAdmissibleValues.of(read, SETS).at("elsewhere").isAny());
        assertTrue(ConjoinedAdmissibleValues.<String>top().at("elsewhere").isAny(),
                "and a conjunction of no readings names nothing at all");
    }

    /**
     * Whether a reading was taken is not how many factors there are.
     *
     * <p>Two readings that name the same position are one factor, since the exact conjunction of
     * those is their product — so counting the factors counts the vocabularies the readings fell
     * into and not the readings. What a caller taking a reading in once needs to know is whether one
     * was taken, and normalising never leaves nothing where a reading went in, so that question is
     * the same of both.
     */
    @Test
    void whetherAReadingWasTakenIsNotHowManyFactorsThereAre() {
        ConjoinedAdmissibleValues<String> nothing = ConjoinedAdmissibleValues.top();
        assertFalse(nothing.hasReadings());

        ConjoinedAdmissibleValues<String> overOneVocabulary =
                ConjoinedAdmissibleValues.of(AdmissibleValues.at("x", just("A")), SETS)
                        .meet(ConjoinedAdmissibleValues.of(
                                AdmissibleValues.at("x", just("B")), SETS));

        assertEquals(1, overOneVocabulary.factors().size(),
                "two readings of one position are one factor");
        assertTrue(overOneVocabulary.hasReadings(), "and two readings were taken all the same");
    }

    /**
     * A tripwire, and not the proof above it.
     *
     * <p>{@link AdmissibleValues#subjects} is what says which positions a reading is about, and
     * everything here rests on it being all of them. It is worked out from the six places a subject
     * is filed under today, and a seventh added tomorrow would leave a reading naming a position
     * that {@code subjects()} does not — so the conjunction would call two overlapping factors
     * disjoint and answer one of them from the other's silence.
     *
     * <p>The same list {@link AdmissibleValues#renamed} rewrites, for the same reason.
     */
    @Test
    void everyPlaceASubjectIsFiledUnderIsOneSubjectsKnowsAbout() {
        RecordComponent[] components = AdmissibleValues.class.getRecordComponents();

        assertEquals(9, components.length,
                "a component was added to a reading. If it is filed under a subject, `subjects()`"
                        + " and `renamed()` both have to reach it; if it is not, say so here: "
                        + List.of(components));
    }

    /** A reading of two positions leaving two alternatives, which is what a choice written across
     *  two positions comes to. */
    private static AdmissibleValues<String> twoAlternatives(String one, String other) {
        return AdmissibleValues.at(one, just("x"))
                .meet(AdmissibleValues.at(other, just("y")), SETS)
                .joinApart(AdmissibleValues.at(one, just("p"))
                        .meet(AdmissibleValues.at(other, just("q")), SETS), SETS);
    }

    private static ValueSet just(String text) {
        return ValueSet.just(Value.text(text));
    }

    private static int alternativesOf(AdmissibleValues<String> read) {
        return read.held() instanceof AdmissibleValues.Held.Alternatives<String> it
                ? it.boxes().size() : 0;
    }
}
