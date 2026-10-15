package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper called on what the call before it left reads each condition along the ways a run can
 * take to it, and the decision it states is one rule for each way a run takes through the chain.
 *
 * <p>The helper hands on nought where the amount fits under the cap and the excess where it does
 * not, so the {@code i}-th condition is whether the amount fits under the first {@code i} caps
 * together. Where the amounts cannot fall below nought, the call after a fit compares nought with a
 * cap and holds of every input: of the {@code 2^k} ways the arms of {@code k} calls could be taken
 * together, {@code k + 1} are some input's, and the others are proved to be none. Where the
 * amounts may be negative every way is some input's, and nothing is closed.
 *
 * <p>Each answer is checked against the helper run in this test, over every amount within the
 * declarations in a small range, and not against a spelling of what the compiler said.
 */
class ATakeChainIsReadAlongOnlyTheWaysARunTakesTest {

    /** A chain of {@code calls} calls of the helper, each on what the call before it left. */
    private static String chain(int calls, boolean noughtOrMore) {
        List<String> caps = new ArrayList<>();
        List<String> takes = new ArrayList<>();
        List<String> fills = new ArrayList<>();
        String rest = "used";
        for (int i = 0; i < calls; i++) {
            caps.add("c" + i + ": MB");
            takes.add("    let (a%d, rest%d) = take(%s, held.c%d)".formatted(i, i, rest, i));
            fills.add("a" + i);
            rest = "rest" + i;
        }
        return """
                module demo

                data MB = Int BOUND
                data Held = { CAPS }

                behavior draw : (used: MB, held: Held) -> List<MB>
                    constructs MB

                let draw (used, held) = {
                TAKES
                    [FILLS, REST]
                }

                let take (used: MB, cap: MB): (MB, MB) =
                    if used.value <= cap.value then (used, MB(0)) else (cap, MB(used.value - cap.value))
                """.replace(" BOUND", noughtOrMore ? "\n    invariant value >= 0" : "")
                .replace("CAPS", String.join(", ", caps))
                .replace("TAKES", String.join("\n", takes))
                .replace("FILLS", String.join(", ", fills))
                .replace("REST", rest);
    }

    /**
     * The same chain written out in the body: each remainder a name bound to the choice, and the
     * next condition comparing that name. A comparison whose side is the choice itself, and not a
     * value its arithmetic stops at, is the other way a reading meets one.
     */
    private static String lets(int calls, boolean noughtOrMore) {
        List<String> caps = new ArrayList<>();
        StringBuilder lets = new StringBuilder();
        String rest = "used.value";
        for (int i = 0; i < calls; i++) {
            caps.add("c" + i + ": MB");
            lets.append("    let r%d = if %s <= held.c%d.value then 0 else %s - held.c%d.value\n"
                    .formatted(i, rest, i, rest, i));
            rest = "r" + i;
        }
        return """
                module demo

                data MB = Int BOUND
                data Held = { CAPS }

                behavior draw : (used: MB, held: Held) -> Int

                let draw (used, held) = {
                LETS    REST
                }
                """.replace(" BOUND", noughtOrMore ? "\n    invariant value >= 0" : "")
                .replace("CAPS", String.join(", ", caps))
                .replace("LETS", lets)
                .replace("REST", rest);
    }

    /** What each condition of the chain comes out as, the helper run here. */
    private static List<Boolean> taking(int calls, Map<String, Long> at) {
        List<Boolean> out = new ArrayList<>();
        long rest = at.get("used");
        for (int i = 0; i < calls; i++) {
            long cap = at.get("c" + i);
            boolean fits = rest <= cap;
            out.add(fits);
            rest = fits ? 0 : rest - cap;
        }
        return out;
    }

    /** {@code conditions} values each chosen by a condition on a position of its own, and their
     *  sum answered: no way through it is closed by another. */
    private static String apart(int conditions) {
        List<String> positions = new ArrayList<>();
        List<String> lets = new ArrayList<>();
        List<String> summed = new ArrayList<>();
        for (int i = 0; i < conditions; i++) {
            positions.add("x" + i + ": Int");
            lets.add("    let v%d = if held.x%d > 0 then 1 else 0".formatted(i, i));
            summed.add("v" + i);
        }
        return """
                module demo

                data Held = { POSITIONS }

                behavior draw : (held: Held) -> Int

                let draw (held) = {
                LETS
                    SUM
                }
                """.replace("POSITIONS", String.join(", ", positions))
                .replace("LETS", String.join("\n", lets))
                .replace("SUM", String.join(" + ", summed));
    }

    private static List<Boolean> each(int conditions, Map<String, Long> at) {
        List<Boolean> out = new ArrayList<>();
        for (int i = 0; i < conditions; i++) {
            out.add(at.get("x" + i) > 0);
        }
        return out;
    }

    /**
     * A model and the run it is checked against.
     *
     * @param atoms the numbers of its input, each as the last part of how the compiler spells it
     * @param least the least each takes in the grid, which the declarations allow
     * @param most  the most
     * @param run   what each condition comes out as on an assignment
     */
    private record Model(String source, List<String> atoms, long least, long most,
                         Function<Map<String, Long>, List<Boolean>> run) {

        /** Every assignment of the grid. */
        List<Map<String, Long>> grid() {
            List<Map<String, Long>> out = new ArrayList<>();
            out.add(Map.of());
            for (String atom : atoms) {
                List<Map<String, Long>> wider = new ArrayList<>();
                for (Map<String, Long> each : out) {
                    for (long value = least; value <= most; value++) {
                        Map<String, Long> one = new LinkedHashMap<>(each);
                        one.put(atom, value);
                        wider.add(one);
                    }
                }
                out = wider;
            }
            return out;
        }

        /** Each way the conditions come out together on some assignment of the grid. */
        Set<List<Boolean>> ways() {
            Set<List<Boolean>> out = new HashSet<>();
            grid().forEach(each -> out.add(run.apply(each)));
            return out;
        }
    }

    private static Model chainModel(int calls, boolean noughtOrMore) {
        return model(chain(calls, noughtOrMore), calls, noughtOrMore);
    }

    private static Model letsModel(int calls, boolean noughtOrMore) {
        return model(lets(calls, noughtOrMore), calls, noughtOrMore);
    }

    private static Model model(String source, int calls, boolean noughtOrMore) {
        List<String> atoms = new ArrayList<>(List.of("used"));
        for (int i = 0; i < calls; i++) {
            atoms.add("c" + i);
        }
        return new Model(source, atoms, noughtOrMore ? 0 : -2, noughtOrMore ? 4 : 2,
                at -> taking(calls, at));
    }

    private static Model apartModel(int conditions) {
        List<String> atoms = new ArrayList<>();
        for (int i = 0; i < conditions; i++) {
            atoms.add("x" + i);
        }
        return new Model(apart(conditions), atoms, -2, 2, at -> each(conditions, at));
    }

    /** What the body states of each condition it reads, as the reading of its meanings has it. */
    private static List<Proposition> stated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("draw");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("draw");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis,
                () -> inputs.reading(rules), reads, rules.symbols(), rules.newtypes());
        return meanings.stated().values().stream().map(each -> each.states()).toList();
    }

    private static DecisionReading decided(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        DecisionEvidence decided = compilation.db()
                .ask(new Adequacy.Decides(compilation.modules().get(0))).value().get("draw");
        assertNotNull(decided, "the rules of the model are read");
        return decided.read();
    }

    /** Whether {@code stated} holds at {@code at}. */
    private static boolean holds(Proposition stated, Map<String, Long> at) {
        return switch (stated) {
            case Proposition.Always always -> always.holds();
            case Proposition.Compared(Relation.Affine(var form, var relation), var held, var _) ->
                    relation.holds(signOf(form, at)) == held;
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, at));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, at));
            default -> throw new AssertionError("a statement this test reads: " + stated.key());
        };
    }

    /** Whether {@code decided} comes out at {@code at} as the rule has it. */
    private static boolean holds(DecidedCondition decided, Map<String, Long> at) {
        return switch (decided) {
            case DecidedCondition.Compared(
                    DecisionCondition.AComparison(var form, var relation), var held) ->
                    relation.holds(signOf(form, at)) == held;
            case DecidedCondition.Held(DecisionCondition.AStatement(var statement), var held) ->
                    holds(statement, at) == held;
            default -> throw new AssertionError("a condition this test reads: " + decided);
        };
    }

    private static boolean holdsAll(DecisionRule rule, Map<String, Long> at) {
        return rule.inOrder().stream().allMatch(each -> holds(each, at));
    }

    /** Which way {@code form} stands to nought at {@code at}. */
    private static <A extends Quantity> int signOf(LinearForm<A> form, Map<String, Long> at) {
        ExactRatio sum = form.constant();
        for (Map.Entry<A, ExactRatio> term : form.coefs().entrySet()) {
            String spelled = term.getKey().spelled();
            Long value = at.get(spelled.substring(spelled.lastIndexOf('.') + 1));
            assertNotNull(value, () -> "a number of the input the model has: " + spelled);
            sum = exact(sum.plus(exact(term.getValue().times(ExactRatio.of(value)))));
        }
        return sum.signum();
    }

    private static ExactRatio exact(ExactAnswer<ExactRatio> answer) {
        if (answer instanceof ExactAnswer.Held<ExactRatio>(var value)) {
            return value;
        }
        throw new AssertionError("small whole numbers are held: " + answer);
    }

    /** Longer than a chain nothing is left out of is read before the figure stops it
     *  ({@link ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest}). */
    @Test
    void aLongChainOfAmountsNoughtOrMoreReadsEveryConditionToTheEnd() {
        for (String source : List.of(chain(12, true), lets(12, true))) {
            List<Proposition> stated = stated(source);

            assertFalse(stated.isEmpty());
            for (Proposition each : stated) {
                assertEquals(List.of(), Proposition.stopsIn(each), each::key);
            }
        }
    }

    @Test
    void eachConditionReadIsTheConditionTheHelperTests() {
        for (Model model : List.of(chainModel(4, true), chainModel(4, false), letsModel(4, true),
                letsModel(4, false))) {
            List<Map<String, Long>> grid = model.grid();
            List<List<Boolean>> runs = grid.stream().map(model.run()).toList();
            int calls = runs.getFirst().size();
            Set<Integer> matched = new HashSet<>();
            for (Proposition stated : stated(model.source())) {
                List<Integer> alike = new ArrayList<>();
                for (int i = 0; i < calls; i++) {
                    boolean same = true;
                    for (int at = 0; at < grid.size() && same; at++) {
                        same = holds(stated, grid.get(at)) == runs.get(at).get(i);
                    }
                    if (same) {
                        alike.add(i);
                    }
                }
                assertFalse(alike.isEmpty(),
                        () -> "a statement is one of the helper's conditions: " + stated.key());
                matched.addAll(alike);
            }
            assertEquals(calls, matched.size(), "every condition of the chain is stated");
        }
    }

    @Test
    void amountsNoughtOrMoreLeaveARuleForEachWayARunTakes() {
        DecisionReading read = rulesAgainstTheRun(chainModel(4, true), 5);

        assertFalse(read.impossible().isEmpty(), "the ways no run takes are proved closed");
    }

    @Test
    void amountsThatMayBeNegativeLeaveEveryWay() {
        DecisionReading read = rulesAgainstTheRun(chainModel(3, false), 8);

        assertEquals(List.of(), read.impossible(), "every way is some input's");
    }

    @Test
    void conditionsOnPositionsOfTheirOwnLeaveEveryWay() {
        DecisionReading read = rulesAgainstTheRun(apartModel(4), 16);

        assertEquals(List.of(), read.impossible(), "every way is some input's");
    }

    /**
     * The rules of {@code model}, checked against its run: each is some assignment's, every
     * assignment it leaves goes one way, and between them they are every way the run takes. And
     * no way said to be no input's is one an assignment takes, or one past which a rule was kept.
     */
    private static DecisionReading rulesAgainstTheRun(Model model, int rules) {
        DecisionReading read = decided(model.source());
        assertInstanceOf(DecisionReading.Enumeration.Complete.class, read.enumeration());
        List<Map<String, Long>> grid = model.grid();
        Set<List<Boolean>> told = new HashSet<>();
        for (DecisionRule rule : read.rules()) {
            Set<List<Boolean>> ways = new HashSet<>();
            for (Map<String, Long> at : grid) {
                if (holdsAll(rule, at)) {
                    ways.add(model.run().apply(at));
                }
            }
            assertEquals(1, ways.size(),
                    () -> "the inputs the rule leaves go one way: " + ways + " of " + rule);
            told.addAll(ways);
        }
        assertEquals(rules, read.rules().size(), () -> "rules: " + read.rules());
        assertEquals(model.ways(), told, "a rule for each way a run takes");
        for (DecisionReading.ImpossiblePath closed : read.impossible()) {
            DecisionRule way = closed.way().rule();
            assertTrue(grid.stream().noneMatch(at -> holdsAll(way, at)),
                    () -> "no input takes " + way);
            for (DecisionRule rule : read.rules()) {
                assertFalse(closed.standsFor(rule), () -> rule + " is past " + way);
            }
        }
        return read;
    }
}
