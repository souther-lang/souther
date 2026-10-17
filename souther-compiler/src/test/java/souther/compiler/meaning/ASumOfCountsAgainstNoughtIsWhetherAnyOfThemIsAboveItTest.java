package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Counts weighed above nought add up to something above nought exactly where one of them is, and
 * then to at least the least weight. So their sum held against a number up to that weight is some
 * element of one of the containers meeting what it counts, held to nought is none doing so, and
 * held against more says how many, which is kept as the relation.
 */
class ASumOfCountsAgainstNoughtIsWhetherAnyOfThemIsAboveItTest {

    private static final TermPath XS = TermPath.of("xs");

    private static final TermPath YS = TermPath.of("ys");

    private static final Quantity.HowManyMeet X = counted(XS);

    private static final Quantity.HowManyMeet Y = counted(YS);

    private static final Proposition EITHER = Proposition.any(List.of(X.someMeets(),
            Y.someMeets()));

    @Test
    void atLeastOneOfTheSumIsSomeElementOfEitherMeetingWhatItCounts() {
        assertEquals(EITHER, stated(1, 1, Rel.GE, 1));
        assertEquals(EITHER, stated(1, 1, Rel.GT, 0));
        assertEquals(EITHER, stated(1, 1, Rel.NE, 0));
    }

    @Test
    void noneOfTheSumIsNoElementOfEitherMeetingIt() {
        assertEquals(EITHER.denied(), stated(1, 1, Rel.EQ, 0));
        assertEquals(EITHER.denied(), stated(1, 1, Rel.LT, 1));
        assertEquals(EITHER.denied(), stated(1, 1, Rel.LE, 0));
    }

    @Test
    void theSumAtOrAboveNoughtIsEveryRow() {
        assertEquals(new Proposition.Always(true), stated(1, 1, Rel.GE, 0));
        assertEquals(new Proposition.Always(false), stated(1, 1, Rel.LT, 0));
    }

    /** {@code 2·x + 3·y} above nought is at least two, so anything up to two is reached by one
     *  element of either; three is not reached by one element of xs. */
    @Test
    void theLeastWeightIsHowFarTheSumIsSureToReach() {
        assertEquals(EITHER, stated(2, 3, Rel.GE, 2));
        assertEquals(EITHER, stated(2, 3, Rel.GT, 1));
        assertInstanceOf(Proposition.Compared.class, stated(2, 3, Rel.GE, 3));
        assertInstanceOf(Proposition.Compared.class, stated(2, 3, Rel.GT, 2));
    }

    @Test
    void aSumHeldPastWhetherAnyIsAboveNoughtSaysHowMany() {
        assertInstanceOf(Proposition.Compared.class, stated(1, 1, Rel.GE, 2));
        assertInstanceOf(Proposition.Compared.class, stated(1, 1, Rel.EQ, 1));
    }

    /** One count can make up for the other, so the difference above nought is no element meeting
     *  anything in particular. */
    @Test
    void aCountTakenAwayIsKeptAsTheRelation() {
        assertInstanceOf(Proposition.Compared.class, stated(1, -1, Rel.GE, 1));
    }

    @Test
    void oneCountComesOutAsItAlwaysDid() {
        assertEquals(X.someMeets(), stated(LinearForm.atom(X), Rel.GE, 1));
        assertEquals(X.someMeets().denied(), stated(LinearForm.atom(X), Rel.EQ, 0));
        assertEquals(new Proposition.Always(false),
                stated(LinearForm.weighing(X, ExactRatio.of(2)), Rel.EQ, 3));
        assertInstanceOf(Proposition.Compared.class, stated(LinearForm.atom(X), Rel.GE, 2));
    }

    /** What is written as some element meeting what is counted is never kept as the relation. */
    @Test
    void aSumOfCountsAgainstNoughtIsNoComparison() {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(sum(1, 1, 1), Rel.GE);
        assertThrows(IllegalArgumentException.class, () -> new Proposition.Compared(
                new Relation.Affine(one.form(), one.proposition()), true));
    }

    private static Quantity.HowManyMeet counted(TermPath container) {
        return new Quantity.HowManyMeet(new DecisionSubject.AnInput(container),
                new Proposition.Truth(new DecisionSubject.AnInput(container.element()), true));
    }

    /** {@code onX·x + onY·y rel against}, as a comparison states it. */
    private static Proposition stated(long onX, long onY, Rel rel, long against) {
        return stated(sum(onX, onY, 0), rel, against);
    }

    /** {@code onX·x + onY·y - against}. */
    private static LinearForm<Quantity> sum(long onX, long onY, long against) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(X, ExactRatio.of(onX));
        coefs.put(Y, ExactRatio.of(onY));
        return new LinearForm<>(ExactRatio.of(-against), coefs);
    }

    /** {@code counts rel against}, for {@code counts} a form with nothing added. */
    private static Proposition stated(LinearForm<Quantity> counts, Rel rel, long against) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(-against), counts.coefs()), rel);
        return Proposition.compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }
}
