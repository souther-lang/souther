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
        CONDITIONS.put("foldOfAStep",
                "List.fold((w, l) -> w + l, 0, List.map(x -> x + 1, ds)) >= 10");
        CONDITIONS.put("foldOfAnUnchangedStep",
                "List.fold((w, l) -> w + l, 0, List.map(x -> x, ds)) >= 10");
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
     * What a step works out at each element is told where its answers are added up, whether the
     * walk adding them is read or not. Each differs from its negative by the operation of the
     * step alone, so the note is the step's and not the total's, which a step that changes
     * nothing adds up the same.
     */
    @Test
    void aStepWorkedOutAtEachElementOfATotalIsToldAsTheStepAloneIs() {
        assertEquals(1, TOLD.get("sumOfAStep").size(), TOLD.toString());
        assertEquals(1, TOLD.get("sumOfAStepWithAProduct").size(), TOLD.toString());
        assertEquals(1, TOLD.get("foldOfAStep").size(), TOLD.toString());
        assertEquals(List.of(), TOLD.get("sumOfAnUnchangedStep"), TOLD.toString());
        assertEquals(List.of(), TOLD.get("foldOfAnUnchangedStep"), TOLD.toString());
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
        StringBuilder model = new StringBuilder("module m\n\ndata Tier = Low | High\n");
        CONDITIONS.forEach((name, condition) -> model.append("\nbehavior ").append(name)
                .append(" : (ds: List<Int>, q: Int, t: Tier) -> Int\nlet ").append(name)
                .append(" (ds, q, t) = if ").append(condition).append(" then 1 else 2\n"));
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
