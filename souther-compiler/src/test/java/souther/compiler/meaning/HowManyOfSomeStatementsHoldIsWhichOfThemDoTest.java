package souther.compiler.meaning;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many of some statements hold, held against a number, is which of them hold: a choice for each
 * that puts the number where the comparison does — written out where the choices are no more than
 * the statements, and otherwise held as the statements and the counts admitted.
 *
 * <p>What a closure states of each value a container was written with is one statement per value,
 * and {@code List.filter(x -> x > 0, [a, a])} holds two of one statement. So two of them is that
 * statement, and one of them is nothing a row can be: the same value meets it twice or not at all.
 */
class HowManyOfSomeStatementsHoldIsWhichOfThemDoTest {

    private static final Proposition P =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("p")), true);

    private static final Proposition Q =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("q")), true);

    @Test
    void twoOfOneStatementWrittenTwiceIsThatStatement() {
        assertEquals(P, howMany(List.of(P, P), Rel.EQ, 2));
    }

    @Test
    void oneOfOneStatementWrittenTwiceIsNoRow() {
        assertEquals(new Proposition.Always(false), howMany(List.of(P, P), Rel.EQ, 1));
    }

    /** One of two is held as the count, and its choices are either of them and not both. */
    @Test
    void oneOfTwoIsEitherOfThemAndNotBoth() {
        assertEquals(new CountsWrittenOut.Written(Proposition.any(List.of(
                        Proposition.all(List.of(P, Q.denied())),
                        Proposition.all(List.of(P.denied(), Q))))),
                CountsWrittenOut.of(howMany(List.of(P, Q), Rel.EQ, 1)));
    }

    /** At least one holding is one of them holding, whatever the other does: a fewest set that
     *  comes to the number, and nothing said of the rest. */
    @Test
    void atLeastOneOfTwoIsEitherOfThem() {
        assertEquals(new CountsWrittenOut.Written(Proposition.any(List.of(P, Q))),
                CountsWrittenOut.of(howMany(List.of(P, Q), Rel.GE, 1)));
    }

    /** At most one holding is the denial of both holding: one of them failing, whatever the other
     *  does. */
    @Test
    void atMostOneOfTwoIsEitherOfThemFailing() {
        assertEquals(Proposition.any(List.of(P.denied(), Q.denied())),
                Proposition.compared(relation(List.of(P, Q), Rel.GE, 2), false));
    }

    @Test
    void denyingTheComparisonDeniesWhichOfThemHold() {
        assertEquals(P.denied(), Proposition.compared(relation(List.of(P, P), Rel.EQ, 2), false));
    }

    /** A statement written twice weighs two: two of three writings is it alone or the other with
     *  it failing — never the other alone. */
    @Test
    void aStatementWrittenTwiceWeighsTwo() {
        assertEquals(Proposition.all(List.of(P, Q.denied())),
                howMany(List.of(P, P, Q), Rel.EQ, 2));
    }

    /**
     * Exactly one of many is held as the count, and its choices are one for each of them and not
     * one for each way they could all come out, for a reader that is handed them.
     */
    @Test
    void exactlyOneOfManyIsOneChoiceForEach() {
        List<Proposition> each = distinct(18);
        assertEquals(new CountsWrittenOut.Written(exactlyOneOf(each)),
                CountsWrittenOut.of(howMany(each, Rel.EQ, 1)));
    }

    /**
     * Exactly one of more, whose choices each name every statement, comes to more parts written
     * out than a step is concluded with, and is held as the count: each statement once, and the
     * one count it admits. Its choices are still what it states, for a reader that asks for them.
     */
    @Test
    void aCountWhoseChoicesComeToMorePartsIsHeldAsTheCount() {
        List<Proposition> each = distinct(70);
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(each, Rel.EQ, 1));

        assertEquals(each.stream().sorted((a, b) -> a.key().compareTo(b.key())).toList(),
                held.statements());
        assertEquals(List.of(1), held.admitted());
        assertTrue(held.weights().stream().allMatch(weight -> weight == 1), held::toString);
        assertEquals(new CountsWrittenOut.Written(exactlyOneOf(each)), CountsWrittenOut.of(held));
    }

    /** Half of eighteen is more choices than are written out, and is held as the count too. */
    @Test
    void moreChoicesThanAreWrittenOutAreHeldAsTheCount() {
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(18), Rel.EQ, 9));

        assertEquals(List.of(9), held.admitted());
    }

    /**
     * A count held as the count is denied as the other counts: no statement is denied and no choice
     * is made, so the denial of a count past what is written out is as small as the count.
     */
    @Test
    void aCountHeldAsTheCountIsDeniedAsTheOtherCounts() {
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(70), Rel.EQ, 1));
        Proposition.SoManyHold denied = assertInstanceOf(Proposition.SoManyHold.class,
                held.denied());

        assertEquals(held.statements(), denied.statements());
        List<Integer> others = new ArrayList<>();
        others.add(0);
        for (int count = 2; count <= 70; count++) {
            others.add(count);
        }
        assertEquals(others, denied.admitted());
        assertEquals(held, denied.denied());
        assertEquals(denied, Proposition.compared(relation(distinct(70), Rel.EQ, 1), false));
    }

    /**
     * Choices more than one condition is read in, or that come to more parts than a reader of
     * them is handed, are handed to none, and which of the two is what the reader is told.
     *
     * <p>Half of eighteen is past how many; exactly one of two hundred and fifty-six is as many
     * choices as one condition is read in, each naming every statement, and past the parts.
     */
    @Test
    void choicesPastWhatAReaderIsHandedAreHandedToNone() {
        assertEquals(new CountsWrittenOut.PastAFigure(CompositionBudget.READINGS_OF_ONE_CONDITION),
                CountsWrittenOut.of(howMany(distinct(18), Rel.EQ, 9)));

        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertEquals(new CountsWrittenOut.PastAFigure(
                        CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO),
                CountsWrittenOut.of(howMany(distinct(most), Rel.EQ, 1)));
        assertEquals(CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO.figure(),
                new WhyNotTaken.MoreChoicesThanAreWrittenOut(
                        CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO).figure()
                        .orElseThrow());
    }

    /**
     * A count past the figure is not mistaken for something else by the readers of what is said of
     * an answer. Remade over the answer, it says which figure it was past; asked only what it is
     * about, it is what its statements are about, which needs no choices; and what a row is held
     * to is the statement as it stands, for whoever asks the row to say the figure.
     */
    @Test
    void aCountPastTheFigureIsSaidSoByWhatIsSaidOfAnAnswer() {
        Proposition half = howMany(distinct(18), Rel.EQ, 9);

        assertEquals(new AnswerAsAnInput.Remade.PastAFigure(
                        CompositionBudget.READINGS_OF_ONE_CONDITION),
                AnswerAsAnInput.of(half, "$answer", null, null, Map.of()));
        assertEquals(Set.of(), AnswerAsAnInput.inputNumbersIn(half),
                "about the input's truths, and so about none of its numbers");
        assertEquals(half, AnswerAsAnInput.ofTheRow(half, Map.of()));
    }

    /**
     * Exactly one of a thousand is past the parts a reader is handed, found by the walk making the
     * choices and not after: each choice names every statement, so the parts pass the figure a few
     * dozen choices in, and the walk stops there — not one thousand choices of a thousand
     * statements each written out whole and counted.
     */
    @Test
    @Timeout(value = 10, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void exactlyOneOfAThousandIsRefusedBeforeItsChoicesAreWrittenOut() {
        assertEquals(new CountsWrittenOut.PastAFigure(
                        CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO),
                CountsWrittenOut.of(howMany(distinct("t", 1000), Rel.EQ, 1)));
    }

    /**
     * The parts the choices of a count are held to are the parts a step is counted in, however
     * deep a statement goes: a statement of thirty parts is thirty parts in every choice that names
     * it, and the parts said of what is handed are those. So a few such statements are written out
     * at what they come to, and a hundred of them are past the figure.
     */
    @Test
    void theChoicesOfStatementsOfManyPartsAreHeldToEveryPartOfThem() {
        Proposition.SoManyHold few = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(ofThirtyParts(12), Rel.EQ, 1));
        WhichOfThemHold.Written written = few.writtenForAReader();
        assertEquals(Conclusion.countingTo(CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO)
                .partsWrittenOut(written.choices()), written.parts());

        assertEquals(new CountsWrittenOut.PastAFigure(
                        CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO),
                CountsWrittenOut.of(howMany(ofThirtyParts(100), Rel.EQ, 1)));
    }

    /** {@code count} statements of their own, each every one of thirty truths of its own. */
    private static List<Proposition> ofThirtyParts(int count) {
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(Proposition.all(distinct("s" + i + "_", 30)));
        }
        return out;
    }

    /**
     * What a reader is handed is held to the figure all together, and not count by count: exactly
     * one of two hundred and fifty is within it alone, and two such counts in one statement are
     * past it.
     */
    @Test
    @Timeout(value = 10, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void twoCountsOneReaderIsHandedAreHeldToOneFigure() {
        Proposition one = howMany(distinct("t", 250), Rel.EQ, 1);
        Proposition other = howMany(distinct("u", 250), Rel.EQ, 1);
        assertInstanceOf(CountsWrittenOut.Written.class, CountsWrittenOut.of(one));
        assertInstanceOf(CountsWrittenOut.Written.class, CountsWrittenOut.of(other));

        assertEquals(new CountsWrittenOut.PastAFigure(
                        CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO),
                CountsWrittenOut.of(Proposition.all(List.of(one, other))));
    }

    /**
     * A count no choice comes to is no choice, found without looking at any: forty statements each
     * written twice come to an even number however many hold, and every set of fewer than twenty
     * of them comes short of thirty-nine.
     */
    @Test
    @Timeout(value = 10, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void aCountNoChoiceComesToIsNoChoiceFoundWithoutLookingAtAny() {
        List<Proposition> twice = new ArrayList<>();
        for (Proposition one : distinct(40)) {
            twice.add(one);
            twice.add(one);
        }

        assertEquals(new Proposition.Always(false), howMany(twice, Rel.EQ, 39));
    }

    /**
     * A count is held as the count whenever it is one, and not by how many choices it would be
     * written out as: neither how many a reading takes in nor how many parts a step concludes with
     * is part of what it states. Only a relation that comes to one choice or none is not a count,
     * and is the statement itself or no row.
     */
    @Test
    void aCountIsHeldAsTheCountWhateverHowManyChoicesItWouldBeWrittenOutAs() {
        int[][] counts = {{2, 1}, {3, 1}, {4, 2}, {5, 4}, {8, 4}, {10, 5}, {11, 5}, {13, 6}};

        for (int[] nk : counts) {
            assertInstanceOf(Proposition.SoManyHold.class,
                    howMany(distinct(nk[0]), Rel.EQ, nk[1]), () -> nk[1] + " of " + nk[0]);
        }
        for (int[] nk : new int[][] {{3, 3}, {3, 0}}) {
            assertTrue(!(howMany(distinct(nk[0]), Rel.EQ, nk[1]) instanceof Proposition.SoManyHold),
                    () -> nk[1] + " of " + nk[0] + " is one choice");
        }
    }

    /**
     * Held as the count or written out, it states the same for every way its statements come out,
     * and its denial states the opposite: the number that hold, weighed by how often each was
     * written, stands to the number as the comparison says.
     */
    @Test
    void heldOrWrittenOutItStatesTheSameCountAndItsDenialTheOpposite() {
        for (int statements = 1; statements <= 6; statements++) {
            List<Proposition> each = new ArrayList<>(distinct(statements));
            // The first statement written twice, so a statement weighs more than one.
            each.add(each.getFirst());
            for (Rel rel : List.of(Rel.EQ, Rel.GE)) {
                for (int against = 0; against <= each.size(); against++) {
                    Proposition stated = howMany(each, rel, against);
                    Proposition denied = Proposition.compared(relation(each, rel, against), false);
                    for (int ways = 0; ways < 1 << each.size(); ways++) {
                        Set<String> holding = holdingIn(each, ways);
                        int count = (int) each.stream()
                                .filter(one -> holds(one, holding)).count();
                        boolean expected = rel.holds(Integer.compare(count, against));
                        int of = statements;
                        int at = against;
                        assertEquals(expected, holds(stated, holding),
                                () -> rel + " " + at + " of " + of + " statements, ways " + holding);
                        assertEquals(!expected, holds(denied, holding),
                                () -> "not " + rel + " " + at + " of " + of + " statements, ways "
                                        + holding);
                    }
                }
            }
        }
    }

    /** The positions of {@code each} that are true when {@code ways} says so, bit by bit. */
    private static Set<String> holdingIn(List<Proposition> each, int ways) {
        Set<String> out = new HashSet<>();
        List<Proposition> once = each.stream().distinct().toList();
        for (int at = 0; at < once.size(); at++) {
            if ((ways >> at & 1) == 1) {
                out.add(((Proposition.Truth) once.get(at)).of().toString());
            }
        }
        return out;
    }

    /** Whether {@code stated} holds where the truths named in {@code holding} are true. */
    private static boolean holds(Proposition stated, Set<String> holding) {
        return switch (stated) {
            case Proposition.Always always -> always.holds();
            case Proposition.Truth truth -> holding.contains(truth.of().toString()) == truth.holds();
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, holding));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, holding));
            case Proposition.SoManyHold counted -> {
                int count = 0;
                for (int at = 0; at < counted.statements().size(); at++) {
                    if (holds(counted.statements().get(at), holding)) {
                        count += counted.weights().get(at);
                    }
                }
                yield counted.admitted().contains(count);
            }
            default -> throw new AssertionError("a statement of truths: " + stated);
        };
    }

    /**
     * A count made over other statements takes out what they say of themselves: one that always
     * holds adds its weight to every count, one that never does adds none, and two written alike
     * are one weighed twice. What is left is the count again, or what it comes to for every row.
     */
    @Test
    void aCountOverSettledAndRepeatedStatementsIsTheCountOfWhatIsLeft() {
        List<Proposition> each = distinct(4);

        assertEquals(Proposition.SoManyHold.counting(each, List.of(1, 1, 1, 1), List.of(1)),
                Proposition.SoManyHold.counting(
                        List.of(each.get(0), each.get(1), each.get(2), each.get(3),
                                new Proposition.Always(true)),
                        List.of(1, 1, 1, 1, 2), List.of(3)));
        assertEquals(Proposition.SoManyHold.counting(each, List.of(1, 1, 1, 1), List.of(2)),
                Proposition.SoManyHold.counting(
                        List.of(each.get(0), each.get(1), each.get(2), each.get(3),
                                new Proposition.Always(false)),
                        List.of(1, 1, 1, 1, 2), List.of(2)));
        assertEquals(Proposition.SoManyHold.counting(List.of(each.get(0), each.get(1)),
                        List.of(2, 1), List.of(1, 2)),
                Proposition.SoManyHold.counting(
                        List.of(each.get(0), each.get(0), each.get(1)), List.of(1, 1, 1),
                        List.of(1, 2)));
        assertEquals(new Proposition.Always(true),
                Proposition.SoManyHold.counting(each, List.of(1, 1, 1, 1), List.of(0, 1, 2, 3, 4)));
        assertEquals(new Proposition.Always(false),
                Proposition.SoManyHold.counting(each, List.of(1, 1, 1, 1), List.of(5)));
        assertEquals(new Proposition.Always(true), Proposition.SoManyHold.counting(
                List.of(new Proposition.Always(true)), List.of(1), List.of(1)));
    }

    /** {@code count} statements, each about a position of its own. */
    private static List<Proposition> distinct(int count) {
        return distinct("t", count);
    }

    /** {@code count} statements, each about a position of its own named from {@code named}. */
    private static List<Proposition> distinct(String named, int count) {
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(named + i)),
                    true));
        }
        return out;
    }

    /** Some one of {@code each} holding and every other failing, written out by hand. */
    private static Proposition exactlyOneOf(List<Proposition> each) {
        List<Proposition> choices = new ArrayList<>();
        for (Proposition holding : each) {
            List<Proposition> parts = new ArrayList<>();
            for (Proposition one : each) {
                parts.add(one == holding ? one : one.denied());
            }
            choices.add(Proposition.all(parts));
        }
        return Proposition.any(choices);
    }

    /** {@code #each - against} standing to nought as {@code rel} says. */
    private static Proposition howMany(List<Proposition> each, Rel rel, long against) {
        return Proposition.compared(relation(each, rel, against), true);
    }

    private static Relation relation(List<Proposition> each, Rel rel, long against) {
        return new Relation.Affine(new LinearForm<>(ExactRatio.of(-against),
                Map.of(new Quantity.HowManyHold(each), ExactRatio.ONE)), rel);
    }
}
