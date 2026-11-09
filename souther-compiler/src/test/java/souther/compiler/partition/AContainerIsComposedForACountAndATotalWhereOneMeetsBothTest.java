package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.function.LongPredicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list of whole numbers composed for how many of them meet a statement and for what they come
 * to holds as many meeting it as the count asks and comes to the total asked; and where some list
 * meets both, one is composed.
 *
 * <p>The oracle is arithmetic and a walk: each container offered is read back number by number,
 * and every list of up to three numbers from a few of them is walked for one meeting both. Over
 * every count from none to two and every total in a range, for two statements: a number above half
 * of what the numbers come to, which reads the total, and a number that is nought, five or ten,
 * which each of the three is alike to and only the middle one of which is a total of one.
 */
class AContainerIsComposedForACountAndATotalWhereOneMeetsBothTest {

    private static final String SOURCE = """
            module g

            data Ok

            behavior counted : (xs: List<Int>) -> Ok
            """;

    private static final Pattern NUMBER = Pattern.compile("-?\\d+");

    /** The input of {@link #SOURCE}, read. */
    private record Read(Quantities measuring, RuleReadingContext reading, TermPath xs,
                        NumericTerm.ValueOf number, NumericTerm total) {}

    /** A statement of one number, as the composer is handed it and as the oracle reads it. */
    private record Statement(String name, Proposition said, TotalAndNumber holds) {}

    @FunctionalInterface
    private interface TotalAndNumber {
        boolean of(long total, long number);
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals("xs")).findFirst().orElseThrow();
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(xs.element());
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(xs.element()), Type.INT, rules.inners(),
                rules.symbols());
        return new Read(input.quantities(rules), reading, xs, number, total);
    }

    private static Statement aboveHalf(Read read) {
        // the total less twice the number is below nought
        return new Statement("above half the total", new Proposition.Compared(
                new Relation.Affine(new LinearForm<>(ExactRatio.ZERO, Map.of(
                        new DecisionAtom.OfTheInput(read.total()), ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(read.number()), ExactRatio.of(-2))),
                        Rel.GE), false),
                (total, number) -> total - 2 * number < 0);
    }

    private static Statement noughtFiveOrTen(Read read) {
        List<Proposition> each = new ArrayList<>();
        for (long at : List.of(0L, 5L, 10L)) {
            each.add(new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                    ExactRatio.of(-at), Map.of(new DecisionAtom.OfTheInput(read.number()),
                            ExactRatio.ONE)), Rel.EQ), true));
        }
        return new Statement("nought, five or ten", Proposition.any(each),
                (total, number) -> number == 0 || number == 5 || number == 10);
    }

    private static TermRealizations.Realization composed(Read read, Statement statement,
                                                         long count, long total) {
        RealizationTarget.ACount counted = new RealizationTarget.ACount(CountedElements.of(
                "counted", new Quantity.HowManyMeet(new DecisionSubject.AnInput(read.xs()),
                        statement.said()), read.measuring(), AnElementMeeting.UNREAD));
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        demands.put(counted, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                new Level.OfTheQuantity(ExactRatio.of(count)))), Count.of(count)));
        ContainerAsAWhole.ATotal asked = new ContainerAsAWhole.ATotal(read.total(),
                new NumericSet.At(Count.of(total)), Count.of(total),
                read.measuring().ordersOf(read.total()));
        return CardinalityComposer.compose(new Type.ListOf(Type.INT), List.of(), read.xs(),
                List.of(counted), List.of(), List.of(), demands, null, List.of(), List.of(asked),
                read.measuring(), read.measuring().region(), read.reading());
    }

    /** The numbers a container offered holds, in order. */
    private static List<Long> numbersOf(FixtureTemplate container) {
        List<Long> out = new ArrayList<>();
        Matcher found = NUMBER.matcher(container.text());
        while (found.find()) {
            out.add(Long.parseLong(found.group()));
        }
        return out;
    }

    private static boolean meetsBoth(List<Long> numbers, Statement statement, long count,
                                     long total) {
        long sum = numbers.stream().mapToLong(Long::longValue).sum();
        long meeting = numbers.stream().filter(each -> statement.holds().of(sum, each)).count();
        return sum == total && meeting == count;
    }

    /** Whether some list of up to three of {@code values} meets both. */
    private static boolean someListMeetsBoth(List<Long> values, Statement statement, long count,
                                             long total) {
        List<List<Long>> lists = new ArrayList<>(List.of(List.of()));
        for (int length = 0; length <= 3; length++) {
            List<List<Long>> longer = new ArrayList<>();
            for (List<Long> list : lists) {
                if (meetsBoth(list, statement, count, total)) {
                    return true;
                }
                for (long value : values) {
                    List<Long> one = new ArrayList<>(list);
                    one.add(value);
                    longer.add(one);
                }
            }
            lists = longer;
        }
        return false;
    }

    private static void holdsOver(Statement statement, List<Long> values, LongPredicate totals,
                                  long least, long most) {
        Read read = read();
        for (long count = 0; count <= 2; count++) {
            for (long total = least; total <= most; total++) {
                if (!totals.test(total)) {
                    continue;
                }
                TermRealizations.Realization composed = composed(read, statement, count, total);
                String said = statement.name() + ", " + count + " of them, coming to " + total
                        + ": " + composed;
                if (composed instanceof TermRealizations.Realization.Built built) {
                    for (FixtureTemplate each : built.values()) {
                        assertTrue(meetsBoth(numbersOf(each), statement, count, total),
                                said + " offers " + each.text());
                    }
                }
                if (someListMeetsBoth(values, statement, count, total)) {
                    assertInstanceOf(TermRealizations.Realization.Built.class, composed, said);
                }
            }
        }
    }

    @Test
    void aboveHalfOfWhatTheyComeTo() {
        Read read = read();
        List<Long> values = new ArrayList<>();
        for (long each = -4; each <= 4; each++) {
            values.add(each);
        }
        holdsOver(aboveHalf(read), values, _ -> true, -4, 4);
    }

    @Test
    void noughtFiveOrTenEachAlikeToTheOthers() {
        Read read = read();
        holdsOver(noughtFiveOrTen(read), List.of(-1L, 0L, 1L, 5L, 10L), _ -> true, -2, 12);
    }

    /** The control the walk is held to: it finds the list the review named, and refuses one that
     *  meets neither. */
    @Test
    void theWalkFindsWhatItIsAskedFor() {
        Read read = read();
        Statement statement = noughtFiveOrTen(read);
        assertTrue(someListMeetsBoth(List.of(0L, 5L, 10L), statement, 1, 5), "[5]");
        assertEquals(false, someListMeetsBoth(List.of(0L, 5L, 10L), statement, 0, 5),
                "every number of them is one of the three");
    }
}
