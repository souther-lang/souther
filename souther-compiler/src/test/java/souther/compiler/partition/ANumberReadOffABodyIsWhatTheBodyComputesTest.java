package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The number a body is read as counts what the body computes.
 *
 * <p>Each number is read off a rule of the body, and then counted over cases by a reference that
 * takes every part of what it counts from the number read: the places it names, the fields it
 * goes down, the key and the value it takes. The language runs the same body over the same cases
 * as an example whose output is the count, and has to answer what the reference counts on every
 * one. So a reading naming another place, field, key or value than the body computes with is told
 * apart from the right one by some case, whatever composes a row toward it.
 */
class ANumberReadOffABodyIsWhatTheBodyComputesTest {

    private static final String MODEL = """
            module probe.computed

            data Forecast = { currency: String, amount: Int }
            data Node = { owner: String, reports: List<Node> }
            data Shelf = { tags: List<Set<Int>> }

            let noForecasts: Map<String, Forecast> = Map.empty

            let own (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                Map.get(node.owner, byOwner) |> Option.map(one -> [ one ])
                    |> Option.withDefault([])

            let under (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ under(r, byOwner), own(node, byOwner),
                          node.reports)

            let howManyCurrencies (node: Node, byOwner: Map<String, Forecast>): Int =
                Set.size(Set.fromList(List.map(.currency, under(node, byOwner))))

            behavior collected : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collected (node, byOwner) = howManyCurrencies(node, byOwner) == 1

            behavior collectedCount : (node: Node, byOwner: Map<String, Forecast>) -> Int
            let collectedCount (node, byOwner) = howManyCurrencies(node, byOwner)

            let howManyTags (s: Shelf): Int =
                Set.size(List.fold((acc, t) -> Set.union(acc, t), Set.empty, s.tags))

            behavior joined : (s: Shelf) -> Bool
            let joined (s) = howManyTags(s) >= 2

            behavior joinedCount : (s: Shelf) -> Int
            let joinedCount (s) = howManyTags(s)
            """;

    private static final Compilation READ = compiled(MODEL);

    /** A node, as the language's record holds it. */
    private static Map<String, Object> node(String owner, Map<?, ?>... reports) {
        return Map.of("owner", owner, "reports", List.of(reports));
    }

    /** The map of forecasts handed beside the tree. No two entries are the same forecast, so how
     *  many entries differ is not how many currencies do. */
    private static Map<String, Map<String, Object>> forecasts(String... ownersAndCurrencies) {
        Map<String, Map<String, Object>> out = new LinkedHashMap<>();
        for (int at = 0; at < ownersAndCurrencies.length; at += 2) {
            out.put(ownersAndCurrencies[at], Map.of("currency", ownersAndCurrencies[at + 1],
                    "amount", out.size() + 1));
        }
        return out;
    }

    private record Case(String says, Map<String, Object> inputs) {}

    private static Case searched(String says, Map<String, Object> root,
                                 Map<String, Map<String, Object>> byOwner) {
        return new Case(says, Map.of("node", root, "byOwner", byOwner));
    }

    private static final List<Case> SEARCHES = List.of(
            searched("nothing is held for any node", node("a", node("b")), forecasts()),
            searched("the root holds one", node("a", node("b")), forecasts("a", "JPY")),
            searched("only a child holds one, and the root holds none",
                    node("a", node("b")), forecasts("b", "JPY")),
            searched("only a grandchild holds one",
                    node("a", node("b", node("c"))), forecasts("c", "JPY")),
            searched("two nodes of one owner name one entry",
                    node("a", node("a"), node("a")), forecasts("a", "JPY")),
            searched("two entries of one value are one value",
                    node("a", node("b")), forecasts("a", "JPY", "b", "JPY")),
            searched("two entries of two values are two",
                    node("a", node("b")), forecasts("a", "JPY", "b", "USD")),
            searched("an entry no node names changes nothing",
                    node("a", node("b")), forecasts("a", "JPY", "z", "USD")),
            searched("an entry no node names changes nothing, with another reached",
                    node("a", node("b"), node("c")),
                    forecasts("a", "JPY", "c", "JPY", "z", "USD")),
            searched("three values from three levels",
                    node("a", node("b", node("c"))),
                    forecasts("a", "JPY", "b", "USD", "c", "EUR")));

    private static Case shelf(String says, List<Set<Integer>> tags) {
        return new Case(says, Map.of("s", Map.of("tags", tags)));
    }

    private static final List<Case> SHELVES = List.of(
            shelf("no set", List.of()),
            shelf("one set of one", List.of(Set.of(1))),
            shelf("one set of two", List.of(Set.of(1, 2))),
            shelf("two sets of the same one", List.of(Set.of(1), Set.of(1))),
            shelf("two sets sharing one", List.of(Set.of(1, 2), Set.of(2, 3))),
            shelf("three sets of different ones", List.of(Set.of(1), Set.of(2), Set.of(3))));

    @Test
    void howManyDifferentValuesASearchCollectsIsWhatTheSearchAnswers() {
        Quantity read = theOnlyNumber("collected");
        assertInstanceOf(Quantity.HowManyDifferentBelow.class, read);
        assertEquals(List.of(0, 1, 1, 1, 1, 1, 2, 1, 1, 3), counted(read, SEARCHES),
                "the cases tell each part of the number apart");
        answered("collectedCount", read, SEARCHES,
                inputs -> "(" + written(inputs.get("node")) + ", "
                        + written(inputs.get("byOwner")) + ")");
    }

    @Test
    void howManyDifferentValuesAWalkOfUnionsGathersIsWhatTheWalkAnswers() {
        Quantity read = theOnlyNumber("joined");
        assertInstanceOf(Quantity.HowManyDifferentAcross.class, read);
        assertEquals(List.of(0, 1, 2, 1, 3, 3), counted(read, SHELVES),
                "the cases tell each part of the number apart");
        answered("joinedCount", read, SHELVES, inputs -> "(" + written(inputs.get("s")) + ")");
    }

    /** {@code read} counted over each case. */
    private static List<Integer> counted(Quantity read, List<Case> cases) {
        return cases.stream().map(each -> counted(read, each.inputs())).toList();
    }

    /** The language answers {@code behavior} on each case with what {@code read} counts there. */
    private static void answered(String behavior, Quantity read, List<Case> cases,
                                 Function<Map<String, Object>, String> written) {
        StringBuilder source = new StringBuilder(MODEL).append("\nexample ").append(behavior)
                .append('\n');
        for (Case each : cases) {
            source.append("    | \"").append(each.says()).append("\" : ")
                    .append(written.apply(each.inputs())).append(" -> ")
                    .append(counted(read, each.inputs())).append('\n');
        }
        Compilation run = compiled(source.toString());
        assertEquals(List.of(), run.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
    }

    /** What {@code read} counts of {@code inputs}, every part taken from it. */
    private static int counted(Quantity read, Map<String, Object> inputs) {
        Set<Object> different = new HashSet<>();
        switch (read) {
            case Quantity.HowManyDifferentAcross across ->
                    different.addAll(valuesAt(inputs, place(across.ofTheOccurrence())));
            case Quantity.HowManyDifferentBelow below -> {
                Map<?, ?> map = (Map<?, ?>) only(valuesAt(inputs, below.map()));
                List<Object> reached = new ArrayList<>(valuesAt(inputs, below.root()));
                for (int at = 0; at < reached.size(); at++) {
                    Object node = reached.get(at);
                    Object entry = map.get(down(node, below.keyAt()));
                    if (entry != null) {
                        different.add(down(entry, below.valueAt()));
                    }
                    for (String field : below.through()) {
                        reached.addAll((Collection<?>) ((Map<?, ?>) node).get(field));
                    }
                }
            }
            default -> throw new IllegalArgumentException("no reference counts " + read);
        }
        return different.size();
    }

    private static TermPath place(DecisionSubject subject) {
        return assertInstanceOf(DecisionSubject.AnInput.class, subject).at();
    }

    /** Every value standing at {@code path} of {@code inputs}, one for each occurrence. */
    private static List<Object> valuesAt(Map<String, Object> inputs, TermPath path) {
        List<Object> here = new ArrayList<>(List.of(inputs.get(path.head())));
        for (TermPath.Step step : path.steps()) {
            List<Object> next = new ArrayList<>();
            for (Object each : here) {
                switch (step) {
                    case TermPath.Step.Field(String name) -> next.add(((Map<?, ?>) each).get(name));
                    case TermPath.Step.Element() -> next.addAll((Collection<?>) each);
                    default -> throw new IllegalArgumentException("no value here has " + step);
                }
            }
            here = next;
        }
        return here;
    }

    /** What {@code value} holds down {@code fields}, each a field of a record. */
    private static Object down(Object value, List<String> fields) {
        Object held = value;
        for (String field : fields) {
            held = ((Map<?, ?>) held).get(field);
        }
        return held;
    }

    private static Object only(List<Object> values) {
        assertEquals(1, values.size(), values::toString);
        return values.getFirst();
    }

    /** {@code value} as the language writes it: a node, a forecast, a shelf, a map of forecasts,
     *  a list of sets of numbers. */
    private static String written(Object value) {
        return switch (value) {
            case Map<?, ?> record when record.containsKey("owner") -> "Node { owner = \""
                    + record.get("owner") + "\", reports = [" + String.join(", ",
                    ((List<?>) record.get("reports")).stream().map(each -> written(each))
                            .toList()) + "] }";
            case Map<?, ?> record when record.containsKey("currency") -> "Forecast { currency = \""
                    + record.get("currency") + "\", amount = " + record.get("amount") + " }";
            case Map<?, ?> record when record.containsKey("tags") -> "Shelf { tags = ["
                    + String.join(", ", ((List<?>) record.get("tags")).stream()
                    .map(each -> "Set.fromList([" + String.join(", ", ((Set<?>) each).stream()
                            .map(String::valueOf).sorted().toList()) + "])").toList()) + "] }";
            case Map<?, ?> map when map.isEmpty() -> "noForecasts";
            case Map<?, ?> map -> "Map.fromList([" + String.join(", ", map.entrySet().stream()
                    .map(entry -> "(\"" + entry.getKey() + "\", " + written(entry.getValue())
                            + ")").toList()) + "])";
            default -> throw new IllegalArgumentException("nothing here writes " + value);
        };
    }

    private static Compilation compiled(String source) {
        Compilation made = Compilation.ofSource(source, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    /** The one number the rule of {@code behavior} is read as comparing. */
    private static Quantity theOnlyNumber(String behavior) {
        String module = READ.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(READ, module);
        Bodies.Elaborated checked = READ.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model compiles: " + READ.errors());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputDomain inputs = READ.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        InputReading reading = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules.symbols(), rules.newtypes(), new ConditionNumbering(module, behavior,
                                ConditionOccurrence.Reading.DIVIDING)),
                reading, true, WhatConditionsState.of(reading)).entries();
        assertEquals(1, stated.size(), () -> "one statement: " + stated);
        RowDemand.ForTheRun run = assertInstanceOf(RowDemand.ForTheRun.class,
                assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst()).demand(),
                () -> "the run decides it: " + stated);
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class,
                run.statement());
        LinearForm<Quantity> form = assertInstanceOf(Relation.Affine.class,
                compared.relation()).form();
        assertEquals(1, form.coefs().size(), () -> "one number: " + form);
        return form.coefs().keySet().iterator().next();
    }
}
