package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.runtime.ConstraintViolation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison is told to be one a run may stop in where some run that reaches it does stop, and
 * is told nothing where none does.
 *
 * <p>The truth is the program run: each condition is compiled and run on the numbers a run stops
 * at, and a run that stops is a {@code ConstraintViolation}. What the report says is held to that
 * and not to what the readings of the comparison came to, so a stop a reading drops, or one it
 * tells where no run stops, is found by the program and not by whoever reads the output.
 *
 * <p>The numbers are the fewest that decide every form below as the ends of an {@code Int}, the
 * numbers beside them, the number whose square passes them, and lists of those did, as ten
 * numbers and sixteen lists were tried against these.
 *
 * <p>What is not told though a run stops is written down in {@link #NOT_TOLD}, one form each
 * with why: a stop the compiler learns to tell moves the form out of it, and a form that is not
 * there and is not told is a stop dropped.
 */
class AComparisonTellsOfAStopWhereARunStopsAndNowhereElseTest {

    private static final long MAX = Long.MAX_VALUE;
    private static final long MIN = Long.MIN_VALUE;

    private static final List<Long> NUMBERS = List.of(0L, MAX - 1, MAX, MIN, 3_037_000_500L);

    private static final List<List<Long>> LISTS = List.of(List.of(), List.of(MAX),
            List.of(MAX - 1), List.of(MIN), List.of(MAX, 1L), List.of(3_037_000_500L),
            List.of(4_611_686_018_427_387_904L, 4_611_686_018_427_387_904L));

    /** Each condition on {@code ds} and {@code q}, by the name it is told under. */
    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    /** What a run stops in and no note says, each with why. */
    private static final Map<String, String> NOT_TOLD = new LinkedHashMap<>();

    static {
        // an operation of the comparison, and the same without it
        FORMS.put("sumOfANumber", "q + 1 <= 10");
        FORMS.put("cancelled", "q + 1 >= q");
        FORMS.put("shifted", "(q + 2) - 1 >= 0");
        FORMS.put("quotient", "(q + 1) / 3 >= 2");
        FORMS.put("remainder", "Int.floorMod(q + 1, 7) == 0");
        FORMS.put("negated", "(0 - (q + 1)) <= 5");
        FORMS.put("absOfASum", "Int.abs(q + 1) >= 0");
        FORMS.put("absOfANumber", "Int.abs(q) >= 0");
        FORMS.put("maxOfASum", "Int.max(q + 1, q) >= q");
        FORMS.put("maxOfANumber", "Int.max(q, q) >= q");
        FORMS.put("productOfTwoNumbers", "List.length(ds) * q >= 3");
        FORMS.put("absInALetBody", "Int.abs({ let a = 1 \n q + a }) >= 0");
        FORMS.put("absInALetBodyUnchanged", "Int.abs({ let a = 1 \n q }) >= 0");
        FORMS.put("noOperation", "q >= 3");
        // a choice: what decides it on every run, and an arm on the runs that take it
        FORMS.put("conditionOfAChoice", "(if q + 1 > 0 then 1 else 2) >= 1");
        FORMS.put("armOfAChoice", "(if q > 5 then q + 1 else 3) >= q");
        FORMS.put("armNoRunTakes", "(if q > 5 && q < 3 then q + 1 else 3) >= q");
        FORMS.put("rightOfAnAnd", "q > 0 && q + 1 > 3");
        // a total, which is worked out exactly before its type holds it
        FORMS.put("totalOfTheElements", "List.sum(ds) >= 10");
        FORMS.put("foldOfTheElements", "List.fold((w, l) -> w + l, 0, ds) >= 10");
        FORMS.put("totalOfAStep", "List.sum(List.map(x -> x + 1, ds)) >= 10");
        FORMS.put("foldOfAStep", "List.fold((w, l) -> w + l, 0, List.map(x -> x + 1, ds)) >= 10");
        FORMS.put("totalOfTakenSteps", "List.sum(List.take(2, List.map(x -> x + 1, ds))) >= 10");
        FORMS.put("totalOfWrittenNumbers", "List.sum([1, 2]) >= 2");
        FORMS.put("totalOfWrittenNumbersPastTheType", "List.sum([9223372036854775807, 1]) >= 2");
        // a step over the elements of a list that is only counted, and the same changing nothing
        FORMS.put("lengthOfAStep", "List.length(List.map(x -> x + 1, ds)) >= 2");
        FORMS.put("lengthOfAnUnchangedStep", "List.length(List.map(x -> x, ds)) >= 2");
        FORMS.put("emptyOfAStep", "List.isEmpty(List.map(x -> x + 1, ds))");
        FORMS.put("lengthOfASortedStep", "List.length(List.sort(List.map(x -> x + 1, ds))) >= 2");
        FORMS.put("lengthOfATakenStep",
                "List.length(List.take(2, List.map(x -> x + 1, ds))) >= 2");
        FORMS.put("lengthOfAFlatStep", "List.length(List.flatMap(x -> [x + 1], ds)) >= 2");
        FORMS.put("lengthOfAStepAtAnIndex",
                "List.length(List.mapIndexed((i, x) -> x + 1, ds)) >= 2");
        FORMS.put("lengthOfACancelledStep", "List.length(List.map(x -> (x + 1) - 1, ds)) >= 2");
        FORMS.put("lengthOfAShiftedStep", "List.length(List.map(x -> (x + 2) - 1, ds)) >= 2");
        FORMS.put("lengthOfATupleStep", "List.length(List.map(x -> (x + 1, 1), ds)) >= 2");
        FORMS.put("lengthOfATupleStepUnchanged", "List.length(List.map(x -> (x, 1), ds)) >= 2");
        FORMS.put("lengthOfAConditionStep",
                "List.length(List.map(x -> if x + 1 > 0 then 1 else 2, ds)) >= 2");
        FORMS.put("lengthOfAConditionStepUnchanged",
                "List.length(List.map(x -> if x > 0 then 1 else 2, ds)) >= 2");
        FORMS.put("everyOfAStep", "List.all(r -> r <= 10, List.map(x -> x + 1, ds))");
        FORMS.put("everyOfAShiftedStep", "List.all(r -> r <= 10, List.map(x -> (x + 2) - 1, ds))");
        FORMS.put("lengthOfAnArmStepNoStop",
                "List.length(List.map(x -> if x < 0 then x + 1 else 0, ds)) >= 2");
        FORMS.put("stepBeside", "List.fold((w, l) -> if l > w then l else w, 0, ds) <= q + 1");

        NOT_TOLD.put("absOfANumber", "a call's own stop, here the least Int having no absolute "
                + "value, is told by no reading as an operation of the call: only what it is "
                + "made of is");
        NOT_TOLD.put("absInALetBodyUnchanged", "the same, in the body of a let");
        NOT_TOLD.put("squareOfANumber", "no product of numbers that share a place is a "
                + "NumericTerm.ProductOf (signed): a line on a product needs factors of their own");
        FORMS.put("squareOfANumber", "q * q >= 3");
        NOT_TOLD.put("totalOfSquares", "the same: the answer x * x is a square, which "
                + "ElementValue holds as no monomial of distinct places");
        FORMS.put("totalOfSquares", "List.sum(List.map(x -> x * x, ds)) >= 10");
        NOT_TOLD.put("totalOfAStepByQ", "the comparison is not read, so there is no range for "
                + "what it works out");
        FORMS.put("totalOfAStepByQ", "List.sum(List.map(x -> x + q, ds)) >= 10");
        NOT_TOLD.put("productOfTheElements", "the comparison is not read: a product of what a "
                + "container holds is no term (FormRange.aTotal asks of a sum)");
        FORMS.put("productOfTheElements", "List.product(ds) >= 10");
        NOT_TOLD.put("maxOfAStep", "the comparison is not read, so there is no range for what "
                + "it works out");
        FORMS.put("maxOfAStep", "Option.withDefault(0, List.max(List.map(x -> x + 1, ds))) >= 3");
        NOT_TOLD.put("maxPlusOne", "the comparison is not read, so there is no range for what "
                + "it works out");
        FORMS.put("maxPlusOne", "Option.withDefault(0, List.max(ds)) + 1 <= 10");
        NOT_TOLD.put("foldOfAProduct", "AddedOfEachElement reads only a step that adds to the "
                + "answer so far; an operation over the running value has no operand that is a "
                + "place of the input");
        FORMS.put("foldOfAProduct", "List.fold((w, l) -> w * l, 1, ds) >= 10");
        NOT_TOLD.put("lengthOfAStepOfAFilter", "the elements a filter keeps stand at no place "
                + "(everyElementAt), and an operation told over the elements cannot carry the test "
                + "that keeps them");
        FORMS.put("lengthOfAStepOfAFilter",
                "List.length(List.map(x -> x + 1, List.filter(y -> y > 0, ds))) >= 2");
        NOT_TOLD.put("lengthOfAnArmStep", "what an arm works out is worked out only where the "
                + "arm is taken, which an operation told over the elements cannot say");
        FORMS.put("lengthOfAnArmStep",
                "List.length(List.map(x -> if x > 5 then x + 1 else 0, ds)) >= 2");
    }

    @Test
    void aComparisonIsToldOfAStopWhereARunStopsAndNowhereElse() throws Exception {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder("module demo\n\n"
                + "data In = { ds: List<Int>, q: Int }\ndata Out = Int\n");
        for (int at = 0; at < names.size(); at++) {
            String condition = FORMS.get(names.get(at)).replaceAll("\\bds\\b", "i.ds")
                    .replaceAll("\\bq\\b", "i.q");
            model.append("\nbehavior b").append(at)
                    .append(" : (i: In) -> Out constructs Out\nlet b").append(at)
                    .append(" (i) = Out { value = if ").append(condition)
                    .append(" then 1 else 2 }\n");
        }
        Map<String, Integer> told = notes(model.toString());
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model.toString()),
                AComparisonTellsOfAStopWhereARunStopsAndNowhereElseTest.class.getClassLoader());
        TreeSet<String> stopsAndNothingTold = new TreeSet<>();
        TreeSet<String> toldAndNoRunStops = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                    .getConstructor().newInstance();
            boolean stops = someRunStops(loader, behavior);
            int notes = told.getOrDefault("b" + at, 0);
            if (stops && notes == 0) {
                stopsAndNothingTold.add(names.get(at));
            }
            if (!stops && notes > 0) {
                toldAndNoRunStops.add(names.get(at));
            }
        }
        assertEquals(new TreeSet<String>(), toldAndNoRunStops,
                "told of a stop, and no run of the numbers tried stops");
        assertEquals(new TreeSet<>(NOT_TOLD.keySet()), stopsAndNothingTold,
                "a run stops and no note says so, beside the forms the compiler cannot yet tell");
    }

    private static boolean someRunStops(ClassLoader loader, Object behavior) throws Exception {
        for (List<Long> list : LISTS) {
            for (long number : NUMBERS) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("ds", list, "q", number));
                try {
                    Codecs.apply(behavior, in);
                } catch (ConstraintViolation stopped) {
                    return true;
                }
            }
        }
        return false;
    }

    /** How many {@code may stop a run} notes each behavior's report holds. */
    private static Map<String, Integer> notes(String model) {
        Compilation compilation = ACompiledModel.measured(model,
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        Pattern header = Pattern.compile("^(\\w+)\\s+implemented\\b.*");
        Map<String, Integer> out = new LinkedHashMap<>();
        String current = null;
        for (String line : AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList()) {
            Matcher started = header.matcher(line);
            if (started.matches()) {
                current = started.group(1);
            } else if (current != null && line.contains("may stop a run")) {
                out.merge(current, 1, Integer::sum);
            }
        }
        return out;
    }
}
