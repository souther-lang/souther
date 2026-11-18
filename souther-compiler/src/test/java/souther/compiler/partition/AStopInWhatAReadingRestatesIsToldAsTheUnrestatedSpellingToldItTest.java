package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation of a comparison that may end a run is told as such wherever the comparison is
 * read: where the arithmetic of the relation cancels it, where it is an element of a list
 * written out, where it stands in an arm of a choice, where two steps of a list are composed, and
 * beside a walk. Each is told the note the same operation gives in a comparison that restates
 * nothing, and an operation no run works out is told of none.
 *
 * <p>One case for each way the operation is lost, all read in one model: a form the same
 * mechanism loses is not another claim.
 */
class AStopInWhatAReadingRestatesIsToldAsTheUnrestatedSpellingToldItTest {

    private static final String THE_STOP = "every run stops in q + 1 where q is at least "
            + "9223372036854775807";

    private static final Map<String, String> CONDITIONS = new LinkedHashMap<>();

    static {
        CONDITIONS.put("control", "q + 1 <= 10");
        CONDITIONS.put("cancelled", "q + 1 >= q");
        CONDITIONS.put("written", "List.all(r -> r >= 4, [q + 1, 3])");
        CONDITIONS.put("arm", "(if q > 5 then q + 1 else 3) >= q");
        CONDITIONS.put("ruleSays", "(q + 1) / 2 >= 3");
        CONDITIONS.put("maxOfAnArm", "Int.max((if q > 5 then q + 1 else 3), 4) >= q");
        CONDITIONS.put("absOfAnArm", "Int.abs(if q > 5 then q + 1 else 3) >= q");
        CONDITIONS.put("maxOfAnArmNoStop", "Int.max((if q > 5 then q - 1 else 3), 4) >= q");
        CONDITIONS.put("maxOfAnArmUnreached",
                "Int.max((if q > 5 && q < 3 then q + 1 else 3), 4) >= q");
        CONDITIONS.put("armInAClosure", "List.all(r -> (if r > 5 then q + 1 else 3) >= q, ds)");
        CONDITIONS.put("armInAClosureNoStop",
                "List.all(r -> (if q > 5 then q - 1 else 3) >= r, ds)");
        CONDITIONS.put("nestedArm", "(if q > 5 then (if q > 7 then q + 1 else 3) else 4) >= q");
        CONDITIONS.put("armOfARule", "(if q > 5 then Int.max(q + 1, 3) else 4) >= q");
        CONDITIONS.put("matchArm", "(match t with | Low -> q + 1 | High -> 3) >= q");
        CONDITIONS.put("matchArmNoStop", "(match t with | Low -> Int.max(q, 3) | High -> 3) >= q");
        CONDITIONS.put("composed",
                "List.all(r -> r <= 10, List.map(x -> x + 1, List.map(y -> y * 2, ds)))");
        CONDITIONS.put("beside",
                "List.fold((w, l) -> if l > w then l else w, 0, ds) <= q + 1");
        CONDITIONS.put("sumOfAStep", "List.sum(List.map(x -> x + 1, ds)) >= 10");
        CONDITIONS.put("sumOfAStepWithAProduct", "List.sum(List.map(x -> x * 2, ds)) >= 10");
        CONDITIONS.put("sumOfAnUnchangedStep", "List.sum(List.map(x -> x, ds)) >= 10");
        CONDITIONS.put("sumOfTheElements", "List.sum(ds) >= 10");
        CONDITIONS.put("foldOfTheElements", "List.fold((w, l) -> w + l, 0, ds) >= 10");
        CONDITIONS.put("sumOfNothing", "List.sum([1, 2]) >= 2");
        CONDITIONS.put("foldOfAStep",
                "List.fold((w, l) -> w + l, 0, List.map(x -> x + 1, ds)) >= 10");
        CONDITIONS.put("foldOfAnUnchangedStep",
                "List.fold((w, l) -> w + l, 0, List.map(x -> x, ds)) >= 10");
        CONDITIONS.put("lengthOfAStep", "List.length(List.map(x -> x + 1, ds)) >= 2");
        CONDITIONS.put("lengthOfAStepUnchanged", "List.length(List.map(x -> x, ds)) >= 2");
        CONDITIONS.put("absOfASum", "Int.abs(q + 1) >= 0");
        CONDITIONS.put("absOfAnUnchangedNumber", "Int.abs(q) >= 0");
        CONDITIONS.put("maxOfASumAndItsOperand", "Int.max(q + 1, q) >= q");
        CONDITIONS.put("maxOfAnUnchangedNumber", "Int.max(q, q) >= q");
        CONDITIONS.put("lengthOfAProduct",
                "List.length(List.map(r -> r.price * r.qty, rs)) >= 2");
        CONDITIONS.put("lengthOfAProductUnchanged",
                "List.length(List.map(r -> r.price, rs)) >= 2");
        CONDITIONS.put("lengthTakeOfAStep",
                "List.length(List.take(2, List.map(x -> x + 1, ds))) >= 2");
        CONDITIONS.put("lengthTakeOfAStepUnchanged",
                "List.length(List.take(2, List.map(x -> x, ds))) >= 2");
        CONDITIONS.put("lengthSortOfAStep",
                "List.length(List.sort(List.map(x -> x + 1, ds))) >= 2");
        CONDITIONS.put("lengthSortOfAStepUnchanged",
                "List.length(List.sort(List.map(x -> x, ds))) >= 2");
        CONDITIONS.put("allOfAStep", "List.all(r -> r <= 10, List.map(x -> x + 1, ds))");
        CONDITIONS.put("allOfAProduct", "List.all(r -> r <= 10, List.map(x -> x * 2, ds))");
        CONDITIONS.put("allOfACancelledStep",
                "List.all(r -> r <= 10, List.map(x -> (x + 1) - 1, ds))");
        CONDITIONS.put("allOfAShiftedStep",
                "List.all(r -> r <= 10, List.map(x -> (x + 2) - 1, ds))");
        CONDITIONS.put("lengthOfACancelledStep",
                "List.length(List.map(x -> (x + 1) - 1, ds)) >= 2");
        CONDITIONS.put("lengthOfAShiftedStep",
                "List.length(List.map(x -> (x + 2) - 1, ds)) >= 2");
        CONDITIONS.put("none", "q >= q");
        CONDITIONS.put("armNoStop", "(if q > 5 then q - 1 else 3) >= q");
        CONDITIONS.put("nestedArmNoStop",
                "(if q > 5 then (if q > 7 then q - 1 else 3) else 4) >= q");
    }

    private static final Map<String, List<String>> TOLD = told();

    @Test
    void anOperationInAComparisonThatRestatesNothingIsTold() {
        assertEquals(1, TOLD.get("control").size(), TOLD.toString());
        assertTrue(TOLD.get("control").getFirst().endsWith(THE_STOP), TOLD.toString());
    }

    @Test
    void anOperationTheRelationCancelsIsToldAsTheControlTellsIt() {
        assertEquals(TOLD.get("control").size(), TOLD.get("cancelled").size(), TOLD.toString());
        assertTrue(TOLD.get("cancelled").getFirst().endsWith(THE_STOP), TOLD.toString());
    }

    @Test
    void anOperationInAListWrittenOutIsToldAsTheControlTellsIt() {
        assertTrue(TOLD.get("written").getFirst().endsWith(THE_STOP), TOLD.toString());
    }

    /** Where the operation is in one arm only, a run that takes that arm may stop; which rows
     *  stop is not said of the others. */
    @Test
    void anOperationInOneArmOfAChoiceIsToldAsOneAMayStop() {
        assertEquals(1, TOLD.get("arm").size(), TOLD.toString());
    }

    /** Where a rule says what its rows get past, what a run works out is still told. */
    @Test
    void anOperationInAComparisonARuleSaysTheRowsOfIsTold() {
        assertEquals(1, TOLD.get("ruleSays").size(), TOLD.toString());
    }

    /** The arms of a choice that is an argument are worked out before the operation picks one. */
    @Test
    void anOperationInAnArmThatIsAnArgumentIsToldWhateverTheOperationPicks() {
        assertEquals(1, TOLD.get("maxOfAnArm").size(), TOLD.toString());
        assertEquals(1, TOLD.get("absOfAnArm").size(), TOLD.toString());
    }

    /** A closure is applied to each element, and what a run works out on an arm it takes there
     *  is worked out wherever that application is made. */
    @Test
    void anOperationInAnArmOfAChoiceInAClosureIsToldAsOneAMayStop() {
        assertEquals(1, TOLD.get("armInAClosure").size(), TOLD.toString());
    }

    /** What a rule kept of an arm is kept through the rules read inside it, as many deep as the
     *  choices are. */
    @Test
    void anArmIsToldThroughTheChoicesAndTheRulesReadInsideIt() {
        assertEquals(1, TOLD.get("nestedArm").size(), TOLD.toString());
        assertEquals(1, TOLD.get("armOfARule").size(), TOLD.toString());
    }

    /** An arm of a match is told as an arm of an if is. */
    @Test
    void anOperationInAnArmOfAMatchIsToldAsOneAMayStop() {
        assertEquals(1, TOLD.get("matchArm").size(), TOLD.toString());
    }

    /** The first step is worked out before the second, so a row is not said to stop in the
     *  second where it stopped in the first, and the first is told. */
    @Test
    void anOperationInAStepComposedWithAnotherIsToldAsTheStepAloneIs() {
        assertEquals(1, TOLD.get("composed").size(), TOLD.toString());
        assertTrue(TOLD.get("composed").getFirst()
                .contains("in 2 * ds[*] where ds[*] is at least"), TOLD.toString());
    }

    /**
     * A total of what a container holds stops a run where the exact total is past an
     * {@code Int}, whatever the elements are, and so does one of what a step makes of them, a
     * step that changes nothing included. A total of numbers written out that lie within the
     * type stops none.
     */
    @Test
    void aTotalOfWhatAContainerHoldsIsToldAsOneAMayStop() {
        for (String form : List.of("sumOfTheElements", "foldOfTheElements", "sumOfAStep",
                "sumOfAStepWithAProduct", "foldOfAStep", "sumOfAnUnchangedStep",
                "foldOfAnUnchangedStep")) {
            assertEquals(1, TOLD.get(form).size(), form + " " + TOLD);
        }
        assertEquals(List.of(), TOLD.get("sumOfNothing"), TOLD.toString());
    }

    /**
     * What a step works out at each element is a run's to stop in where nothing is added up, as
     * where the list it makes is counted or asked to be empty, whatever is made of it between.
     * Each differs from its negative by the operation of the step alone.
     */
    @Test
    void aStepWorkedOutAtEachElementOfAListThatIsCountedIsToldAsOneAMayStop() {
        for (String form : List.of("lengthOfAStep", "lengthSortOfAStep", "lengthTakeOfAStep",
                "lengthOfAProduct")) {
            assertEquals(1, TOLD.get(form).size(), form + " " + TOLD);
            assertEquals(List.of(), TOLD.get(form + "Unchanged"), form + " " + TOLD);
        }
    }

    /**
     * What an element comes to stops a run at the operation the closure writes, where it comes to
     * it, whatever the closure's answer is simplified to: {@code (x + 1) - 1} is {@code x} and a
     * run stops at the {@code x + 1}; {@code (x + 2) - 1} is {@code x + 1} and a run stops at the
     * {@code x + 2}, an element sooner. The note says the operation and where it is past the type.
     */
    @Test
    void aStopOfAnElementIsToldAtTheOperationTheClosureWritesIt() {
        assertTrue(TOLD.get("allOfAStep").getFirst().contains(
                "in ds[*] + 1 where ds[*] is at least 9223372036854775807"), TOLD.toString());
        assertTrue(TOLD.get("allOfAProduct").getFirst().contains(
                "in 2 * ds[*] where ds[*] is at least 4611686018427387904"), TOLD.toString());
        assertTrue(TOLD.get("allOfACancelledStep").getFirst().contains(
                "in ds[*] + 1 where ds[*] is at least 9223372036854775807"), TOLD.toString());
        assertTrue(TOLD.get("allOfAShiftedStep").getFirst().contains(
                "in ds[*] + 2 where ds[*] is at least 9223372036854775806"), TOLD.toString());
        assertEquals(1, TOLD.get("lengthOfACancelledStep").size(), TOLD.toString());
        assertEquals(1, TOLD.get("lengthOfAShiftedStep").size(), TOLD.toString());
    }

    /**
     * What a restated comparison holds aside is worked out all the same: {@code Int.abs} of a
     * sum is worked out after the sum, and the larger of a sum and a number after both. Each
     * differs from its negative by the operation alone.
     */
    @Test
    void anOperationUnderAValueTheReadingHoldsAsideIsToldAsOneAMayStop() {
        assertEquals(1, TOLD.get("absOfASum").size(), TOLD.toString());
        assertEquals(List.of(), TOLD.get("absOfAnUnchangedNumber"), TOLD.toString());
        assertEquals(1, TOLD.get("maxOfASumAndItsOperand").size(), TOLD.toString());
        assertEquals(List.of(), TOLD.get("maxOfAnUnchangedNumber"), TOLD.toString());
    }

    /** The other side of a comparison of a walk is worked out whatever the walk answers. */
    @Test
    void anOperationBesideAWalkThatEndsNoRunIsToldAsTheControlTellsIt() {
        assertTrue(TOLD.get("beside").getFirst().endsWith(THE_STOP), TOLD.toString());
    }

    @Test
    void nothingIsToldWhereNoRunWorksTheOperationOut() {
        assertEquals(List.of(), TOLD.get("none"));
        assertEquals(List.of(), TOLD.get("armNoStop"));
        assertEquals(List.of(), TOLD.get("nestedArmNoStop"));
        assertEquals(List.of(), TOLD.get("armInAClosureNoStop"));
        assertEquals(List.of(), TOLD.get("maxOfAnArmNoStop"));
        assertEquals(List.of(), TOLD.get("maxOfAnArmUnreached"));
        assertEquals(List.of(), TOLD.get("matchArmNoStop"));
    }

    /** The notes of each behavior, each of the conditions read once, as the model says them. */
    private static Map<String, List<String>> told() {
        StringBuilder model = new StringBuilder("module m\n\ndata Tier = Low | High\n"
                + "data Row = { price: Int, qty: Int }\n");
        CONDITIONS.forEach((name, condition) -> model.append("\nbehavior ").append(name)
                .append(" : (ds: List<Int>, q: Int, t: Tier, rs: List<Row>) -> Int\nlet ")
                .append(name).append(" (ds, q, t, rs) = if ").append(condition)
                .append(" then 1 else 2\n"));
        Compilation compilation = ACompiledModel.measured(model.toString(),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        Pattern header = Pattern.compile("^(\\w+)\\s+implemented\\b.*");
        Map<String, List<String>> out = new LinkedHashMap<>();
        List<String> current = null;
        for (String line : AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList()) {
            Matcher started = header.matcher(line);
            if (started.matches()) {
                current = out.computeIfAbsent(started.group(1), _ -> new ArrayList<>());
            } else if (current != null && line.contains("may stop a run")) {
                current.add(line);
            }
        }
        return out;
    }
}
