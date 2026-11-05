package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader that holds a statement of a remainder against another reads the two as one exactly
 * where {@link ARemainderMoved} does, and what they leave is what working each remainder out says.
 *
 * <p>Drawn at random from a fixed seed: ways of statements of remainders of one form moved by
 * numbers either way, of the form weighed twice over, of a number inside a container, of a form
 * weighed by a half, by two divisors, each leaving a run of remainders. Held against working each
 * remainder out by {@code Math.floorMod}: a way closes exactly where the statements of one
 * remainder leave none of it in common; a row is composed at exactly the remainders the statements
 * of its own remainder leave, by either standing that composes one; and statements free to be met
 * together are asked together exactly where they leave a remainder between them. Statements of a
 * number inside a container, or of a form weighed by what is not whole, are read as one with
 * nothing, and leave every remainder.
 */
class EveryReaderOfARemainderMovedByANumberReadsItAsOneTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("r").then("a"));
    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("r").then("d"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("r").then("y"));
    private static final NumericTerm ELEMENT =
            new NumericTerm.ValueOf(TermPath.of("r").then("xs").element());

    /** The forms drawn, the first two read as remainders of themselves and the others not. */
    private static final List<Map<NumericTerm, ExactRatio>> FORMS = List.of(
            weighing(A, ExactRatio.ONE, D, ExactRatio.of(-1)),
            weighing(A, ExactRatio.of(2), D, ExactRatio.of(-2)),
            Map.of(ELEMENT, ExactRatio.ONE),
            Map.of(A, ExactRatio.of(BigInteger.ONE, BigInteger.TWO)));
    private static final int READ_AS_ONE = 2;

    private static final long[] DIVISORS = {7, 5};

    /** A statement drawn: which form, moved by what, by which divisor, leaving which run. */
    private record Drawn(int form, long moved, long divisor, long low, long high) {

        boolean readAsOne() {
            return form < READ_AS_ONE;
        }

        boolean ofTheRemainderOf(Drawn other) {
            return readAsOne() && form == other.form && divisor == other.divisor;
        }

        /** Whether this holds where the remainder of the form unmoved is {@code unmoved}. */
        boolean holdsAt(long unmoved) {
            long left = Math.floorMod(unmoved + moved, divisor);
            return low <= left && left <= high;
        }

        RowDemand.OnARemainder demand() {
            Quantity.RemainderOfADividend remainder = Quantity.RemainderOfADividend.ofTheInput(
                    FLOOR_MOD, new LinearForm<>(ExactRatio.of(moved), FORMS.get(form)),
                    BigInteger.valueOf(divisor));
            return new RowDemand.OnARemainder(remainder,
                    WholeNumberRuns.one(BigInteger.valueOf(low), BigInteger.valueOf(high)));
        }

        UndividedByARelation.OnAWay onAWay() {
            Set<TermPath> positions = new LinkedHashSet<>();
            FORMS.get(form).keySet().forEach(term -> positions.add(term.subjectPath()));
            return new UndividedByARelation.OnAWay(positions, false, null, null, null,
                    UndividedByARelation.OnAWay.PartsLeftAlone.NONE, null, demand());
        }
    }

    @Test
    void aWayClosesExactlyWhereTheStatementsOfOneRemainderLeaveNoneOfIt() {
        SearchRegion region = region();
        Random random = new Random(3023);
        int closed = 0;
        int open = 0;
        for (int drawn = 0; drawn < 2000; drawn++) {
            List<Drawn> statements = way(random);
            boolean noneLeft = false;
            for (Drawn each : statements) {
                noneLeft |= each.readAsOne() && leftOf(each, 0, statements).isEmpty();
            }
            Reachability read = Reachability.of(
                    new WayToTheBorder(List.<OnTheWay>copyOf(onTheWay(statements))), region);
            assertEquals(noneLeft, read instanceof Reachability.NumbersLeaveNone,
                    () -> statements + " came to " + read);
            if (noneLeft) {
                closed++;
            } else {
                open++;
            }
        }
        assertTrue(closed > 100 && open > 100, closed + " closed, " + open + " open");
    }

    @Test
    void aRowIsComposedAtExactlyTheRemaindersTheStatementsOfItsOwnLeave() {
        SearchRegion region = region();
        Random random = new Random(3024);
        int narrowed = 0;
        int notReadAsOne = 0;
        for (int drawn = 0; drawn < 2000; drawn++) {
            List<Drawn> statements = way(random);
            Drawn own = statement(random);
            Reachability.Reaching way = new Reachability.Reaching(region, Requirements.NONE,
                    TruthsAsked.NONE, onTheWay(statements), Reachability.Ways.ONE, List.of(),
                    Optional.empty());
            List<Long> expected = own.readAsOne() ? leftOf(own, own.moved, statements)
                    : every(own.divisor);
            LinearForm<NumericTerm> dividend =
                    new LinearForm<>(ExactRatio.of(own.moved), FORMS.get(own.form));
            BigInteger divisor = BigInteger.valueOf(own.divisor);
            Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
            FORMS.get(own.form).keySet().forEach(term -> on.put(term, Carrier.WHOLE));
            Criterion where = new Criterion.AtTheLevel(Level.OfTheQuantity.of(0));
            Standing alone = new Standing.OfARemainder(dividend, on, LevelSpace.steppingBy(
                    ExactRatio.ONE), divisor, where).alongTheWay(way);
            Standing withAForm = new Standing.OfARemainderAndAForm(dividend, on, divisor,
                    Standing.OfARemainderAndAForm.every(divisor),
                    new LinearForm<>(ExactRatio.ZERO, Map.of(Y, ExactRatio.ONE)),
                    Map.of(Y, Carrier.WHOLE), LevelSpace.steppingBy(ExactRatio.ONE), where)
                    .alongTheWay(way);
            assertEquals(expected, held(((Standing.OfARemainder) alone).remainders(), own.divisor),
                    () -> own + " along " + statements);
            assertEquals(expected,
                    held(((Standing.OfARemainderAndAForm) withAForm).remainders(), own.divisor),
                    () -> own + " beside a form along " + statements);
            if (!own.readAsOne()) {
                notReadAsOne++;
            } else if (expected.size() < own.divisor) {
                narrowed++;
            }
        }
        assertTrue(narrowed > 100 && notReadAsOne > 100,
                narrowed + " narrowed, " + notReadAsOne + " of no remainder read as one");
    }

    @Test
    void statementsOfOneRemainderAreAskedTogetherExactlyWhereTheyLeaveOneBetweenThem() {
        Random random = new Random(3025);
        int together = 0;
        int apart = 0;
        for (int drawn = 0; drawn < 2000; drawn++) {
            List<Drawn> statements = way(random);
            Drawn first = statements.get(0);
            for (Drawn each : statements) {
                assertEquals(first.ofTheRemainderOf(each),
                        UndividedByARelation.sameRemainder(first.onAWay(), each.onAWay()),
                        () -> first + " beside " + each);
            }
            List<Drawn> ofOne = statements.stream().filter(first::ofTheRemainderOf).toList();
            boolean between = first.readAsOne() && !leftOf(first, 0, ofOne).isEmpty();
            assertEquals(between, UndividedByARelation.allowTogether(
                    ofOne.isEmpty() ? List.of(first.onAWay())
                            : ofOne.stream().map(Drawn::onAWay).toList()),
                    () -> "together: " + ofOne + " of " + statements);
            if (between && ofOne.size() > 1) {
                together++;
            } else if (ofOne.size() > 1) {
                apart++;
            }
        }
        assertTrue(together > 100 && apart > 100, together + " together, " + apart + " apart");
    }

    /**
     * The remainders of {@code own}'s form, moved by {@code moved}, at which every statement of
     * its remainder holds — worked out from each remainder of the form unmoved.
     */
    private static List<Long> leftOf(Drawn own, long moved, List<Drawn> statements) {
        List<Long> out = new ArrayList<>();
        for (long r = 0; r < own.divisor; r++) {
            long unmoved = Math.floorMod(r - moved, own.divisor);
            boolean held = true;
            for (Drawn each : statements) {
                if (own.ofTheRemainderOf(each) && !each.holdsAt(unmoved)) {
                    held = false;
                }
            }
            if (held) {
                out.add(r);
            }
        }
        return out;
    }

    private static List<Long> held(WholeNumberRuns runs, long divisor) {
        List<Long> out = new ArrayList<>();
        for (long r = 0; r < divisor; r++) {
            if (runs.holds(BigInteger.valueOf(r))) {
                out.add(r);
            }
        }
        return out;
    }

    private static List<Long> every(long divisor) {
        return held(WholeNumberRuns.one(BigInteger.ZERO, BigInteger.valueOf(divisor - 1)),
                divisor);
    }

    /** One to four statements, most of the first form by seven so that some meet. */
    private static List<Drawn> way(Random random) {
        List<Drawn> out = new ArrayList<>();
        for (int at = 0; at < 1 + random.nextInt(4); at++) {
            out.add(statement(random));
        }
        return out;
    }

    private static Drawn statement(Random random) {
        int form = random.nextInt(3) == 0 ? random.nextInt(FORMS.size()) : 0;
        long divisor = random.nextInt(4) == 0 ? DIVISORS[1] : DIVISORS[0];
        long low = random.nextInt((int) divisor);
        long high = low + random.nextInt((int) (divisor - low));
        return new Drawn(form, random.nextInt(19) - 9L, divisor, low, high);
    }

    private static List<OnTheWay.TakenIn> onTheWay(List<Drawn> statements) {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        statements.forEach(each -> out.add(
                new OnTheWay.TakenIn(WHERE, each.demand(), NamedElements.NONE)));
        return out;
    }

    private static Map<NumericTerm, ExactRatio> weighing(NumericTerm one, ExactRatio by,
                                                         NumericTerm other, ExactRatio otherBy) {
        Map<NumericTerm, ExactRatio> out = new LinkedHashMap<>();
        out.put(one, by);
        out.put(other, otherBy);
        return out;
    }

    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, d: Int, y: Int, xs: List<Int> }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """, "Main");
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m")).quantities().region();
    }
}
