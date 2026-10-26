package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Stream;

/**
 * Rows built for the two ways round the order of a repeated key, from a row that already stands at
 * the rule.
 *
 * <p>A composer writes the elements of a container alike, so it cannot write a key held twice by
 * elements that differ elsewhere. The row it did write is read back as the values its run
 * observed, and the container is rewritten there: its first element is kept in two copies that hold
 * the same value at the key and different values in one other field, in both orders. What is
 * written back goes through {@link ObservedFixtures}, so a candidate is spelled the way any other
 * value of the position is.
 *
 * <p>These are candidates and no evidence. Whether the order decides the statement, and whether the
 * row still stands at the rule, are for a run to say ({@link CasesTheRowsTook#casesSeenBy}).
 */
public final class KeyOrderCandidates {

    /** The most distinct values of one kind that the copies of an element are given between them. */
    static final int MOST_VALUES_OF_A_KIND = 6;

    /** The most candidates one row is rewritten into. */
    static final int MOST_CANDIDATES = 48;

    private KeyOrderCandidates() {
    }

    /**
     * Whether a row can be rewritten for {@code target}: the container is reached through fields
     * and elements only, and the key is a field path of its elements.
     */
    public static boolean canBuildFor(CaseOfAStatement.KeyOrder target) {
        return keyWithinAnElement(target.order()) != null && onlyFieldsAndElements(
                target.order().container());
    }

    /**
     * The rows that write {@code base}, whose run observed {@code seen}, with the container of
     * {@code target} holding a key twice. None where the container holds nothing in {@code seen}
     * or the values around it cannot be rewritten.
     *
     * @param base the row the candidates are rewrites of
     * @param seen the values its run observed, one per parameter
     * @param subject what the row's parameters are and how a value of each is written
     */
    public static Stream<RowToRun> refining(CaseOfAStatement.KeyOrder target, RowToRun base,
                                            List<ObservedValue> seen, MeasuredInput subject) {
        List<String> key = keyWithinAnElement(target.order());
        TermPath container = target.order().container();
        int parameter = subject.parameters().indexOf(container.head());
        if (key == null || !onlyFieldsAndElements(container) || parameter < 0
                || parameter >= seen.size() || parameter >= base.inputs().size()) {
            return Stream.empty();
        }
        Map<Class<?>, Set<ObservedValue>> pool = new HashMap<>();
        seen.forEach(each -> gather(each, pool));
        List<ObservedValue> rewritten = new ArrayList<>();
        rewrite(seen.get(parameter), container.steps(), 0, key.getFirst(),
                fieldsTheStatementReads(target, container), pool, rewritten);
        // Written one at a time as the caller asks for them: the first to be evidence of the case
        // ends the search, and the rest are never spelled.
        return rewritten.stream()
                .map(each -> ObservedFixtures.of(each, subject.types().get(parameter),
                        subject.ruleReading()))
                .filter(ObservedFixtures.Writing.Written.class::isInstance)
                .map(written -> {
                    List<FixtureTemplate> inputs = new ArrayList<>(base.inputs());
                    inputs.set(parameter,
                            ((ObservedFixtures.Writing.Written<FixtureTemplate>) written).value());
                    return new RowToRun(inputs, base.answers());
                });
    }

    /**
     * The fields of an element that the statement reads, or null where it is not known which: a
     * field it does not read cannot change what it comes to, so only these are given other values.
     */
    private static Set<String> fieldsTheStatementReads(CaseOfAStatement.KeyOrder target,
                                                       TermPath container) {
        Set<String> fields = new LinkedHashSet<>();
        PositionsAStatementReads.everyPlaceOf(target.statement()).ifPresent(places -> {
            List<TermPath.Step> within = container.steps();
            for (TermPath place : places) {
                List<TermPath.Step> steps = place.steps();
                if (place.head().equals(container.head()) && steps.size() > within.size() + 1
                        && steps.subList(0, within.size()).equals(within)
                        && steps.get(within.size()) instanceof TermPath.Step.Element
                        && steps.get(within.size() + 1) instanceof TermPath.Step.Field(
                                String name)) {
                    fields.add(name);
                }
            }
        });
        return fields.isEmpty() ? null : fields;
    }

    /** The fields from an element of the container to the key, or null where the key is not so. */
    private static List<String> keyWithinAnElement(StandingAtAPoint.OrderOfAKey order) {
        List<TermPath.Step> container = order.container().steps();
        List<TermPath.Step> position = order.position().steps();
        if (!order.container().head().equals(order.position().head())
                || position.size() <= container.size() + 1
                || !position.subList(0, container.size()).equals(container)
                || !(position.get(container.size()) instanceof TermPath.Step.Element)) {
            return null;
        }
        List<String> fields = new ArrayList<>();
        for (TermPath.Step each : position.subList(container.size() + 1, position.size())) {
            if (!(each instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            fields.add(name);
        }
        return fields;
    }

    private static boolean onlyFieldsAndElements(TermPath container) {
        return container.steps().stream().allMatch(each -> each instanceof TermPath.Step.Field
                || each instanceof TermPath.Step.Element);
    }

    /** The scalars a row holds, by kind: the values a copy of an element may be given. A whole
     *  number brings its neighbours, which are the values a comparison against it is cut by. */
    private static void gather(ObservedValue value, Map<Class<?>, Set<ObservedValue>> pool) {
        switch (value) {
            case ObservedValue.Integer(long n) -> {
                Set<ObservedValue> ints = pool.computeIfAbsent(ObservedValue.Integer.class,
                        _ -> new LinkedHashSet<>());
                ints.add(value);
                if (n > Long.MIN_VALUE) {
                    ints.add(new ObservedValue.Integer(n - 1));
                }
                if (n < Long.MAX_VALUE) {
                    ints.add(new ObservedValue.Integer(n + 1));
                }
            }
            case ObservedValue.Decimal _, ObservedValue.Text _, ObservedValue.Bool _,
                 ObservedValue.Temporal _ -> pool.computeIfAbsent(value.getClass(),
                    _ -> new LinkedHashSet<>()).add(value);
            // In the order of the names: a record's fields are held unordered, and the values a
            // copy is given, and so the row found, must not depend on which way a run hashed them.
            case ObservedValue.Constructed made -> new TreeMap<>(made.fields()).values()
                    .forEach(each -> gather(each, pool));
            case ObservedValue.Sequence sequence -> sequence.elements()
                    .forEach(each -> gather(each, pool));
            case ObservedValue.Mapping mapping -> mapping.entries().forEach(entry -> {
                gather(entry.key(), pool);
                gather(entry.value(), pool);
            });
            case ObservedValue.Unit _, ObservedValue.Absent _, ObservedValue.Unknown _,
                 ObservedValue.Truncated _ -> { }
        }
    }

    /**
     * Every value {@code value} comes to with the container {@code steps[at..]} leads to holding a
     * key twice, added to {@code out}.
     */
    private static void rewrite(ObservedValue value, List<TermPath.Step> steps, int at,
                                String keyField, Set<String> reads,
                                Map<Class<?>, Set<ObservedValue>> pool, List<ObservedValue> out) {
        if (out.size() >= MOST_CANDIDATES) {
            return;
        }
        if (at == steps.size()) {
            if (value instanceof ObservedValue.Sequence(List<ObservedValue> elements)
                    && !elements.isEmpty()
                    && elements.getFirst() instanceof ObservedValue.Constructed first) {
                for (List<ObservedValue> held : pairsOf(first, keyField, reads, pool)) {
                    out.add(new ObservedValue.Sequence(held));
                }
            }
            return;
        }
        switch (steps.get(at)) {
            case TermPath.Step.Field(String name) -> {
                if (value instanceof ObservedValue.Constructed made && made.field(name) != null) {
                    List<ObservedValue> inside = new ArrayList<>();
                    rewrite(made.field(name), steps, at + 1, keyField, reads, pool, inside);
                    for (ObservedValue each : inside) {
                        Map<String, ObservedValue> fields = new LinkedHashMap<>(made.fields());
                        fields.put(name, each);
                        out.add(new ObservedValue.Constructed(made.type(), fields));
                    }
                }
            }
            case TermPath.Step.Element _ -> {
                if (value instanceof ObservedValue.Sequence(List<ObservedValue> elements)) {
                    for (int one = 0; one < elements.size(); one++) {
                        List<ObservedValue> inside = new ArrayList<>();
                        rewrite(elements.get(one), steps, at + 1, keyField, reads, pool, inside);
                        for (ObservedValue each : inside) {
                            List<ObservedValue> held = new ArrayList<>(elements);
                            held.set(one, each);
                            out.add(new ObservedValue.Sequence(held));
                        }
                    }
                }
            }
            case TermPath.Step.Key _, TermPath.Step.Refine _ -> { }
        }
    }

    /**
     * The two-element lists made of {@code first}, kept at its key, with one other field given each
     * ordered pair of the values a row holds of its kind.
     */
    private static List<List<ObservedValue>> pairsOf(ObservedValue.Constructed first,
                                                     String keyField, Set<String> reads,
                                                     Map<Class<?>, Set<ObservedValue>> pool) {
        List<List<ObservedValue>> out = new ArrayList<>();
        for (Map.Entry<String, ObservedValue> field : new TreeMap<>(first.fields()).entrySet()) {
            Set<ObservedValue> kind = pool.get(field.getValue().getClass());
            if (field.getKey().equals(keyField) || kind == null
                    || (reads != null && !reads.contains(field.getKey()))) {
                continue;
            }
            List<ObservedValue> values = kind.stream().limit(MOST_VALUES_OF_A_KIND).toList();
            for (ObservedValue a : values) {
                for (ObservedValue b : values) {
                    if (!a.equals(b)) {
                        out.add(List.of(with(first, field.getKey(), a),
                                with(first, field.getKey(), b)));
                    }
                }
            }
        }
        return out;
    }

    private static ObservedValue with(ObservedValue.Constructed made, String field,
                                      ObservedValue value) {
        Map<String, ObservedValue> fields = new LinkedHashMap<>(made.fields());
        fields.put(field, value);
        return new ObservedValue.Constructed(made.type(), fields);
    }
}
