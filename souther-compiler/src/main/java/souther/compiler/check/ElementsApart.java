package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * What the elements of a list or a set are to be apart at: each a run of fields taken from an
 * element, empty for the element itself.
 *
 * <p>A property of the container and not of any one element. A set holds no value twice, which is
 * what a set is; a list may, until a rule says no two of its elements come to one answer of a
 * closure ({@link BoundOperationFacts.NoTwoAlike}). What building one has to know is the same in
 * both cases — which part of an element two elements may not share — so the two arrive here as one
 * answer and a builder never asks which kind of container it holds.
 *
 * <p>Wherever the rule is written. A newtype's rule about its value keeps apart the elements of
 * every value wearing the name; a record's rule about one of its fields keeps apart the elements of
 * the value at that field, and the record is what knows it — so a builder of a value at a field is
 * told by what holds it ({@link #heldAt}), as it is told how many the field holds.
 *
 * <p>Read off what each rule states ({@link InvariantStatements}), so a rule stated through a
 * helper is the rule written out. A closure is read where it takes an element to the element itself
 * or to a run of its fields, and a container where it is a value of the declaration or a run of
 * fields read off one; anything else says something this does not follow, and the rule is left to
 * the decoder that runs it. Nothing here records that: a rule read no further is the reading of
 * values' to account for, and an empty answer here is no claim that the elements may repeat.
 *
 * <p>Only the runs a builder has to keep apart. Elements apart at {@code sku} are apart as wholes,
 * and two records apart at {@code a.b} are apart at {@code a}, so a run that a longer one starts
 * with is left out: what is kept apart at the longer one is apart at it already.
 */
public final class ElementsApart {

    /** The field a newtype's value is bound under, which is what a rule on the newtype names. */
    private static final String THE_VALUE = "value";

    /**
     * What the elements of a position of {@code shape} are to be apart at, given what the rules
     * keep them apart at — those on each name it wears and those of what holds it — nothing where
     * they may repeat.
     *
     * <p>Handed the rules' answers rather than reading them, so that a caller reading a position
     * from every point a search visits can keep each answer for as long as its rules stand.
     */
    public static List<List<String>> of(Shape shape, List<List<String>> keptApartByTheRules) {
        if (!(shape instanceof Shape.Sequence sequence)) {
            return List.of();
        }
        List<List<String>> at = new ArrayList<>();
        if (sequence.kind() == Shape.Sequence.Kind.SET) {
            at.add(List.of());
        }
        at.addAll(keptApartByTheRules);
        return longestOnly(at);
    }

    /**
     * What the rules written on {@code named} keep apart, by where the container is: the value
     * itself ({@link RuleKey#THE_VALUE}) for a name wrapping one, a run of fields for a record or
     * for what a name wraps. Each rule's run as it is written, none dropped for another.
     */
    public static Map<RuleKey, List<List<String>>> writtenOn(TypeSymbol.AtModule named,
                                                             RuleReadingSource source) {
        Map<BindingId, String> fields = new HashMap<>();
        source.bindings().of(named).forEach((name, binding) -> fields.put(binding, name));
        if (fields.isEmpty()) {
            return Map.of();
        }
        boolean record = source.kinds().of(named.key()) == DeclarationKind.PRODUCT
                && !source.newtypes().of(named.key());
        Map<RuleKey, List<List<String>>> out = new LinkedHashMap<>();
        InvariantStatements statements = null;
        for (DeclaredClauses.OnAName written : DeclaredClauses.of(List.of(named), source)) {
            for (DeclaredClauses.Conjunct each : written.conjuncts()) {
                if (statements == null) {
                    statements = InvariantStatements.ofTheCalls(source);
                }
                List<InvariantStatement> states = statements.of(each.part());
                if (states == null) {
                    continue;
                }
                for (InvariantStatement one : states) {
                    if (!(one instanceof InvariantStatement.Applies(var _,
                            Core.PreservedCall call))) {
                        continue;
                    }
                    Stated stated = stated(call);
                    RuleKey where = stated == null ? null
                            : placeOf(stated.container(), fields, record);
                    if (where != null) {
                        out.computeIfAbsent(where, _ -> new ArrayList<>()).add(stated.run());
                    }
                }
            }
        }
        Map<RuleKey, List<List<String>>> kept = new LinkedHashMap<>();
        out.forEach((where, runs) -> kept.put(where, List.copyOf(runs)));
        return Map.copyOf(kept);
    }

    /**
     * What the rules of a value of {@code root}, and of every value a run of fields from it passes
     * through on the way to {@code path}, keep the elements of the value at {@code path} apart at.
     *
     * <p>Every one of them, because each is a rule the value at the end is held to: a record's rule
     * about {@code a.ks} and the rule of the record at {@code a} about its own {@code ks} are two
     * rules about one list. The names the value at the end wears are not among them — those are
     * the position's own, and its reader asks them of the position.
     *
     * @param written what the rules written on a name keep apart ({@link #writtenOn}), handed in so
     *                that a caller asking about many paths reads each name once
     */
    public static List<List<String>> heldAt(Type root, RuleKey path,
                                            Function<TypeSymbol.AtModule,
                                                    Map<RuleKey, List<List<String>>>> written,
                                            RuleReadingSource source) {
        List<String> steps = path.steps();
        List<List<String>> out = new ArrayList<>();
        Type at = root;
        for (int i = 0; i < steps.size(); i++) {
            TypeView view = TypeView.of(at, source.inners(), source.symbols(), source.kinds(),
                    source.sums());
            RuleKey rest = new RuleKey(steps.subList(i, steps.size()));
            for (TypeSymbol wears : view.wrappers()) {
                if (wears instanceof TypeSymbol.AtModule named) {
                    out.addAll(written.apply(named).getOrDefault(rest, List.of()));
                }
            }
            if (!(view.shape() instanceof Shape.Product record)) {
                break;
            }
            if (record.name() instanceof TypeSymbol.AtModule named) {
                out.addAll(written.apply(named).getOrDefault(rest, List.of()));
            }
            at = record.fields().get(steps.get(i));
            if (at == null) {
                break;
            }
        }
        return longestOnly(out);
    }

    /**
     * What the builders of the value at {@code path} of a value of {@code named} keep its elements
     * apart at: the rules of {@code named} and of every value on the way there ({@link #heldAt}),
     * and the rules of each name the value at the end wears.
     *
     * <p>The answer a reading of the rules is held to. What a reader may say was taken in about how
     * a container's elements stand to each other is what the containers composed for it keep, so
     * it is asked here, of the builders' own reading, and not worked out again over the clause:
     * worked out again, a rule written under a choice whose other side is dead would be taken in
     * while the builders, which read conjuncts only, are never told of it.
     *
     * @param there   the type standing at {@code path}, whose names are the position's own
     * @param written what the rules written on a name keep apart ({@link #writtenOn}), handed in
     *                so that a caller asking about many paths reads each name once
     */
    public static List<List<String>> keptAt(TypeSymbol.AtModule named, RuleKey path, Type there,
                                            Function<TypeSymbol.AtModule,
                                                    Map<RuleKey, List<List<String>>>> written,
                                            RuleReadingSource source) {
        TypeView view = TypeView.of(there, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        // Only a container has elements to keep apart, and no name's rules are read for the rest.
        if (!(view.shape() instanceof Shape.Sequence)) {
            return List.of();
        }
        List<List<String>> rules = new ArrayList<>(
                heldAt(new Type.Ref(named), path, written, source));
        if (path.isTheValueItself()) {
            rules.addAll(written.apply(named).getOrDefault(RuleKey.THE_VALUE, List.of()));
        }
        for (TypeSymbol wears : view.wrappers()) {
            if (wears instanceof TypeSymbol.AtModule worn) {
                rules.addAll(written.apply(worn).getOrDefault(RuleKey.THE_VALUE, List.of()));
            }
        }
        return of(view.shape(), rules);
    }

    /**
     * Whether elements kept apart at every run of {@code kept} are apart at {@code run}.
     *
     * <p>Apart at a longer run is apart at every run it starts with — two records apart at
     * {@code a.b} are apart at {@code a} — which is why {@link #of} keeps the longest alone.
     */
    public static boolean covers(List<List<String>> kept, List<String> run) {
        return kept.stream().anyMatch(each -> each.size() >= run.size()
                && each.subList(0, run.size()).equals(run));
    }

    /**
     * Where {@code container} is among the values of a declaration whose fields are bound at
     * {@code fields}, or null where it is no value of it or no run of fields read off one.
     *
     * <p>A newtype's one field is its value, so a run read off it is a run under the value; a
     * record's fields are each a place of their own.
     */
    private static RuleKey placeOf(Core container, Map<BindingId, String> fields,
                                   boolean record) {
        List<String> read = readOffABinding(container);
        if (read == null) {
            return null;
        }
        String field = fields.get(bindingUnder(container));
        if (field == null) {
            return null;
        }
        if (record) {
            List<String> steps = new ArrayList<>();
            steps.add(field);
            steps.addAll(read);
            return new RuleKey(steps);
        }
        return field.equals(THE_VALUE) ? new RuleKey(read) : null;
    }

    /**
     * Whether {@code container} is a value bound somewhere or a run of fields read off one, which
     * is the only kind of container this reads a rule of.
     *
     * <p>Asked by the reading of what a position may hold, so that a rule it calls one about the
     * elements of a container is a rule the builders of that container are told.
     */
    public static boolean readsAPlace(Core container) {
        return readOffABinding(container) != null;
    }

    /** The fields read off a binding to reach {@code e}, outermost first, or null where it is not
     *  reached that way. */
    private static List<String> readOffABinding(Core e) {
        return readOffABinding(e, null);
    }

    /** {@link #readOffABinding(Core)}, leaving out a newtype's own {@code value} where
     *  {@code newtypes} is given. */
    private static List<String> readOffABinding(Core e, DeclarationNewtypes newtypes) {
        ReadOff off = readOff(e, newtypes);
        return off.holder() instanceof Core.Read ? off.path().steps() : null;
    }

    /**
     * A value and the run of fields read off it.
     *
     * @param holder the value the first field is read off, or the value itself where none is
     * @param path   the fields read, outermost first, as a rule of the holder names them
     */
    public record ReadOff(Core holder, RuleKey path) {

        public ReadOff {
            Objects.requireNonNull(holder, "fields are read off some value");
            Objects.requireNonNull(path, "a value is read off its holder by some run of fields");
        }
    }

    /**
     * What {@code e} is read off, and by which fields: the rules of the holder about the value at
     * that run are rules about {@code e} ({@link #heldAt}). A newtype's own {@code value} is no
     * step, as a place of a value names its fields.
     */
    public static ReadOff readOff(Core e, DeclarationNewtypes newtypes) {
        List<String> run = new ArrayList<>();
        Core at = Core.withoutStanding(e);
        while (true) {
            switch (at) {
                case Core.FieldAccess access -> {
                    if (newtypes == null
                            || Location.isStep(access.target().type(), access.field(), newtypes)) {
                        run.add(access.field());
                    }
                    at = Core.withoutStanding(access.target());
                }
                case Core.FieldProjection projection -> {
                    Type from = projection.base().type();
                    List<String> steps = new ArrayList<>();
                    for (Core.FieldProjection.Step each : projection.steps().inOrder()) {
                        if (newtypes == null || Location.isStep(from, each.field(), newtypes)) {
                            steps.add(each.field());
                        }
                        from = each.type();
                    }
                    run.addAll(steps.reversed());
                    at = Core.withoutStanding(projection.base());
                }
                default -> {
                    return new ReadOff(at, new RuleKey(run.reversed()));
                }
            }
        }
    }

    /** The binding {@code e} is read off, where {@link #readOffABinding} reaches one. */
    private static BindingId bindingUnder(Core e) {
        Core at = Core.withoutStanding(e);
        while (true) {
            switch (at) {
                case Core.Read read -> {
                    return read.binding();
                }
                case Core.FieldAccess access -> at = Core.withoutStanding(access.target());
                case Core.FieldProjection projection ->
                        at = Core.withoutStanding(projection.base());
                default -> {
                    return null;
                }
            }
        }
    }

    /**
     * What a call says no two elements of share, and at which run of fields of an element.
     *
     * @param container the value whose elements it is about, as the call was handed it
     * @param run       the fields its closure reads off an element, empty for the element itself
     */
    public record Stated(Core container, List<String> run) {

        public Stated {
            run = List.copyOf(run);
        }
    }

    /**
     * What {@code call} keeps apart, or null where it says nothing of the kind or its closure is
     * none this reads.
     *
     * <p>The one place a call is recognised as keeping elements apart. A reader that asks it of a
     * value it is building and a reader that asks what a position may hold ask the same question
     * of the same call, and each makes of the answer what its own reading can hold.
     */
    public static Stated stated(Core.PreservedCall call) {
        return stated(call, null);
    }

    /**
     * {@link #stated(Core.PreservedCall)}, with the run named as a place of a value names its
     * fields: a newtype's own {@code value} is the value itself and no step of it
     * ({@link Location#isStep}). Where {@code newtypes} is null the run is as the closure wrote it.
     */
    public static Stated stated(Core.PreservedCall call, DeclarationNewtypes newtypes) {
        BoundOperationFacts.NoTwoAlike alike =
                DefaultBoundOperationFacts.get().statesNoTwoAlike(call.operation());
        if (alike == null) {
            return null;
        }
        List<String> run = runTaken(call.args().get(alike.by().position()), newtypes);
        return run == null ? null
                : new Stated(call.args().get(alike.container().position()), run);
    }

    /**
     * The run of fields {@code call} says no two elements of the value bound at {@code container}
     * share, or null where it says no such thing of that value or its closure is none this reads.
     */
    public static List<String> apartAt(Core.PreservedCall call, BindingId container) {
        Stated stated = stated(call);
        return stated != null
                && Core.withoutStanding(stated.container()) instanceof Core.Read read
                && read.binding().equals(container) ? stated.run() : null;
    }

    /** The fields {@code closure} reads off its one parameter in order, or null where it does
     *  anything else with it. */
    public static List<String> runTaken(Core closure, DeclarationNewtypes newtypes) {
        if (!(Core.withoutStanding(closure) instanceof Core.Block block)
                || block.params().size() != 1) {
            return null;
        }
        Core body = block.body();
        return block.params().getFirst().binding().equals(bindingUnder(body))
                ? readOffABinding(body, newtypes) : null;
    }

    /** Elements apart at every run of {@code one} and every run of {@code other}, as one answer of
     *  the kind {@link #of} gives. */
    public static List<List<String>> meet(List<List<String>> one, List<List<String>> other) {
        List<List<String>> both = new ArrayList<>(one);
        both.addAll(other);
        return longestOnly(both);
    }

    /** Each run once, and none that a longer one starts with. */
    private static List<List<String>> longestOnly(List<List<String>> runs) {
        List<List<String>> out = new ArrayList<>();
        for (List<String> each : runs) {
            boolean covered = runs.stream().anyMatch(other -> other.size() > each.size()
                    && other.subList(0, each.size()).equals(each));
            if (!covered && !out.contains(each)) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    private ElementsApart() {}
}
