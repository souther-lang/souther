package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A domain read where the one it was made from had been read reads the rules that reading every
 * rule it was told from the start reads.
 *
 * <p>A domain asked at every step of a path reads what that step said onto what the step before
 * read, and one asked only at the end reads everything from the start. Which of the two a domain
 * took is how often it happened to be asked, and nothing a reader of the rules may see. So each
 * step here is taken twice, once asked along the way and once not, and the two are held to read the
 * same rules in the same order.
 *
 * <p>The steps are the ones where reading onto an earlier reading has something to get right: a
 * bound on a form said looser, tighter, at the same value with the end left out, and said again; a
 * rule that is not a bound said again; and two paths carried on from one said together, which says
 * every rule of the one they share a second time.
 */
class RulesReadOntoAnEarlierReadingAreTheRulesReadFromTheStartTest {

    private static final String A = "a";
    private static final String B = "b";

    private static final Map<String, Granularity> DENSE =
            Map.of(A, Granularity.DENSE, B, Granularity.DENSE);

    /** {@code atom - n}. */
    private static LinearForm<String> from(String atom, long n) {
        return LinearForm.atomMinusConstant(atom, ExactRatio.of(n));
    }

    /** {@code a + b - n}. */
    private static ExactAnswer<LinearForm<String>> bothFrom(long n) {
        return LinearForm.sum(List.of(LinearForm.atom(A), LinearForm.atom(B),
                LinearForm.constant(ExactRatio.of(-n))));
    }

    private static UnaryOperator<NumericDomain<String>> saying(LinearForm<String> f, Rel rel) {
        return d -> d.assume(f, rel, DENSE);
    }

    private static UnaryOperator<NumericDomain<String>> saying(ExactAnswer<LinearForm<String>> f,
                                                               Rel rel) {
        return d -> d.assume(f, rel, DENSE);
    }

    private static NumericDomain<String> top() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
    }

    /** {@code steps} taken from {@code from}, read at every one of them when {@code asked}. */
    private static List<NumericDomain<String>> taken(NumericDomain<String> from,
                                                     List<UnaryOperator<NumericDomain<String>>> steps,
                                                     boolean asked) {
        List<NumericDomain<String>> out = new ArrayList<>();
        NumericDomain<String> at = from;
        for (UnaryOperator<NumericDomain<String>> step : steps) {
            at = step.apply(at);
            if (asked) {
                at.rulesRead();
            }
            out.add(at);
        }
        return out;
    }

    @Test
    void aPathReadAtEveryStepReadsWhatItReadsFromTheStart() {
        List<UnaryOperator<NumericDomain<String>>> steps = List.of(
                saying(from(A, 5), Rel.LE),
                saying(from(A, 7), Rel.LE),
                saying(from(A, 3), Rel.LE),
                saying(from(A, 3), Rel.LT),
                saying(from(A, 3), Rel.LE),
                saying(from(A, 1), Rel.GE),
                saying(from(A, 2), Rel.NE),
                saying(from(B, 9), Rel.LE),
                saying(from(A, 2), Rel.NE),
                saying(bothFrom(10), Rel.LE),
                saying(LinearForm.difference(A, B), Rel.EQ),
                saying(LinearForm.difference(A, B), Rel.EQ),
                saying(bothFrom(8), Rel.LE),
                saying(from(A, 5), Rel.LE),
                saying(from(B, 2), Rel.GE));

        List<NumericDomain<String>> alongTheWay = taken(top(), steps, true);
        for (int upTo = 1; upTo <= steps.size(); upTo++) {
            NumericDomain<String> fromTheStart = taken(top(), steps.subList(0, upTo), false).getLast();
            assertEquals(fromTheStart.rulesRead(), alongTheWay.get(upTo - 1).rulesRead(),
                    "after step " + upTo);
        }
    }

    @Test
    void twoPathsFromOneSaidTogetherReadWhatTheyReadFromTheStart() {
        List<UnaryOperator<NumericDomain<String>>> shared = List.of(
                saying(from(A, 5), Rel.LE),
                saying(from(A, 2), Rel.NE));
        List<UnaryOperator<NumericDomain<String>>> one = List.of(
                saying(from(A, 3), Rel.LE),
                saying(from(B, 4), Rel.NE));
        List<UnaryOperator<NumericDomain<String>>> other = List.of(
                saying(from(B, 4), Rel.LE),
                saying(from(A, 4), Rel.LE),
                saying(from(B, 4), Rel.NE));

        List<NumericDomain<String>> read = new ArrayList<>();
        for (boolean asked : List.of(true, false)) {
            NumericDomain<String> before = taken(top(), shared, asked).getLast();
            NumericDomain<String> together = taken(before, one, asked).getLast()
                    .meet(taken(before, other, asked).getLast());
            read.add(together);
        }

        assertEquals(read.get(1).rulesRead(), read.get(0).rulesRead());
    }
}
