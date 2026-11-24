package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An operator a run works out on some runs only — in a closure an {@code Option.map} applies
 * where there is a value — is not told where it answers, and is left over what its operands read.
 * What it may stop a run on is the places those are read off, and nothing where it is shown to
 * stop none: the number it comes to, from the numbers its operands lie between, lies where it
 * answers.
 *
 * <p>The behavior relates the code of each item to the keys of the prices, and works out a label
 * of each priced item before it. A label that stops no run, or stops one only on places apart
 * from the code, leaves the relation reached at every value of both ({@code rule_relating_two_values},
 * as with no label). One that may stop a run on the code ties it, and the relation is not shown
 * reached at every key of the prices. It is still reached at every code: a row holding the prices
 * empty beside any code works out no label, and gets to the relation.
 *
 * <p>A remainder by a written divisor lies from nought to below it whatever its dividend is,
 * and its third rounded down from nought to three; one more than either is far inside an
 * {@code Int}. A remainder plus a free {@code Int}, a product past what an {@code Int} holds, and a
 * remainder by nought may each stop a run on the code.
 */
class AnOperatorOverANumberWithARangeIsAskedOverThatRangeTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { closeDate: Date, code: String }
            data Prices = { known: Map<String, Int> }
            """;

    private static final String JUDGED = """

            behavior %1$s : (items: List<Item>, start: Int, m: Int, prices: Prices) -> Bool
            let %1$s (items, start, m, prices) = {
                let labels = List.map(i -> Map.get(i.code, prices.known)
                    |> Option.map(p -> String.fromInt(%2$s)), items)
                List.length(labels) == 0
                    || List.all(i -> Map.containsKey(i.code, prices.known), items)
            }
            """;

    private static final String OF_THE_CODE = "Int.floorMod(String.length(i.code), 12)";

    private static final String OF_TWO =
            "Int.floorMod(String.length(i.code) + Date.day(i.closeDate), 12)";

    /** Each label, by name, and whether it leaves the relation read. */
    private static final Map<String, Case> CASES = cases();

    /**
     * @param read          whether the label leaves the relation read at both places
     * @param readPastNoKey where it does not, whether the code is read all the same, past a row
     *                      holding the prices empty
     */
    private record Case(String label, boolean read, boolean readPastNoKey) {

        Case(String label, boolean read) {
            this(label, read, !read);
        }
    }

    private static Map<String, Case> cases() {
        Map<String, Case> out = new LinkedHashMap<>();
        out.put("none", new Case("p", true));
        // The quarter of a year that starts at a month: the difference may pass an Int on the
        // start, which is no place of the relation, and the rounding and the one after it stop
        // no run.
        out.put("quarterOf", new Case("Rational.toInt(DOWN,"
                + " Int.floorMod(Date.month(i.closeDate) - start + 12, 12) / 3) + 1", true));
        out.put("onePastAMonthsRemainder",
                new Case("Int.floorMod(Date.day(i.closeDate) - start + 12, 12) + 1", true));
        out.put("aRemainder", new Case(OF_THE_CODE, true));
        out.put("onePastARemainder", new Case(OF_THE_CODE + " + 1", true));
        out.put("aThird", new Case("Rational.toInt(DOWN, " + OF_THE_CODE + " / 3)", true));
        out.put("onePastAThird",
                new Case("Rational.toInt(DOWN, " + OF_THE_CODE + " / 3) + 1", true));
        out.put("onePastARemainderBelowNought",
                new Case("Int.floorMod(String.length(i.code), -12) + 1", true));
        out.put("aRemainderOfTwo", new Case(OF_TWO, true));
        out.put("onePastARemainderOfTwo", new Case(OF_TWO + " + 1", true));
        out.put("onePastAThirdOfTwo",
                new Case("Rational.toInt(DOWN, " + OF_TWO + " / 3) + 1", true));
        out.put("onePastALength", new Case("String.length(i.code) + 1", true));
        out.put("aRemainderAndAFreeInt", new Case(OF_THE_CODE + " + m", false));
        out.put("aRemainderOfTwoAndAFreeInt", new Case(OF_TWO + " + m", false));
        out.put("aRemainderPastAnInt", new Case(OF_THE_CODE + " * 1000000000000000000", false));
        out.put("aRemainderOfTwoPastAnInt", new Case(OF_TWO + " * 1000000000000000000", false));
        // A remainder by nought is said to stop a run wherever the label is worked out, and is not
        // a stop the reading lets go of past a row holding the prices empty.
        out.put("aRemainderByNought",
                new Case("Int.floorMod(String.length(i.code), 0) + 1", false, false));
        out.put("aLengthAndAFreeInt", new Case("String.length(i.code) + m", false));
        // May stop a run, on the places its dividend is read off and on the free Int, none of
        // which the relation reads.
        out.put("aRemainderOfADateAndAFreeInt", new Case("Int.floorMod(Date.day(i.closeDate)"
                + " + Date.month(i.closeDate), 12) + m", true));
        // What the product comes to is asked of its factors, and not of the type it answers in.
        out.put("aProductOfTwoNumbers",
                new Case("String.length(i.code) * Date.day(i.closeDate) * m", false));
        return out;
    }

    /** Every case measured, by name: one model, compiled and measured once for the class. */
    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        CASES.forEach((name, each) -> source.append(JUDGED.formatted(name, each.label())));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    private static List<String> readAs(String name, UndividedPosition.Reason reason) {
        PartitionEvidence evidence = MEASURED.get(name);
        assertNotNull(evidence, () -> name + " is measured");
        return evidence.notRead().stream().filter(each -> each.reason() == reason)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    @Test
    void aLabelThatStopsNoRunOnTheCodeLeavesTheRelationReadAndOneThatMayTiesIt() {
        List<String> relation = List.of("items[*].code", "prices.known[key]");
        Map<String, List<List<String>>> expected = new LinkedHashMap<>();
        Map<String, List<List<String>>> actual = new LinkedHashMap<>();
        CASES.forEach((name, each) -> {
            expected.put(name, each.read() ? List.of(relation, List.of())
                    : each.readPastNoKey()
                    ? List.of(List.of("items[*].code"), List.of("prices.known[key]"))
                    : List.of(List.of(), relation));
            actual.put(name, List.of(
                    readAs(name, UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                    readAs(name, UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)));
        });
        assertEquals(expected, actual);
    }
}
