package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * What the elements of a list or a set are to be apart at: each a run of fields taken from an
 * element, empty for the element itself.
 *
 * <p>A property of the container and not of any one element. A set holds no value twice, which is
 * what a set is; a list may, until a rule on a name it wears says no two of its elements come to
 * one answer of a closure ({@link BoundOperationFacts.NoTwoAlike}). What building one has to know
 * is the same in both cases — which part of an element two elements may not share — so the two
 * arrive here as one answer and a builder never asks which kind of container it holds.
 *
 * <p>Read off what each rule states ({@link InvariantStatements}), so a rule stated through a
 * helper is the rule written out. A closure is read where it takes an element to the element itself
 * or to a run of its fields; any other closure says something this does not follow, and the rule is
 * left to the decoder that runs it. Nothing here records that: a rule read no further is the
 * reading of values' to account for, and an empty answer here is no claim that the elements may
 * repeat.
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
     * on each name it wears keep them apart at ({@link #writtenOn}) — nothing where they may
     * repeat.
     *
     * <p>Handed the names' answers rather than reading them, so that a caller reading a position
     * from every point a search visits can keep each name's answer for as long as its rules stand.
     */
    public static List<List<String>> of(Shape shape, List<List<String>> writtenOnItsNames) {
        if (!(shape instanceof Shape.Sequence sequence)) {
            return List.of();
        }
        List<List<String>> at = new ArrayList<>();
        if (sequence.kind() == Shape.Sequence.Kind.SET) {
            at.add(List.of());
        }
        at.addAll(writtenOnItsNames);
        return longestOnly(at);
    }

    /** What the rules written on {@code named} keep the elements of its value apart at, each rule's
     *  run as it is written and none of them dropped for another. */
    public static List<List<String>> writtenOn(TypeSymbol.AtModule named,
                                               RuleReadingSource source) {
        BindingId value = source.bindings().of(named).get(THE_VALUE);
        if (value == null) {
            return List.of();
        }
        List<List<String>> at = new ArrayList<>();
        InvariantStatements statements = null;
        for (DeclaredClauses.OnAName written : DeclaredClauses.of(List.of(named), source)) {
            for (DeclaredClauses.Conjunct each : written.conjuncts()) {
                if (statements == null) {
                    statements = InvariantStatements.of(source);
                }
                List<InvariantStatement> states = statements.of(each.part());
                if (states == null) {
                    continue;
                }
                for (InvariantStatement one : states) {
                    if (one instanceof InvariantStatement.Applies(var _, Core.PreservedCall call)) {
                        List<String> run = apartAt(call, value);
                        if (run != null) {
                            at.add(run);
                        }
                    }
                }
            }
        }
        return List.copyOf(at);
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
        BoundOperationFacts.NoTwoAlike alike =
                DefaultBoundOperationFacts.get().statesNoTwoAlike(call.operation());
        if (alike == null) {
            return null;
        }
        List<String> run = runTaken(call.args().get(alike.by().position()));
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
    private static List<String> runTaken(Core closure) {
        if (!(Core.withoutStanding(closure) instanceof Core.Block block)
                || block.params().size() != 1) {
            return null;
        }
        BindingId element = block.params().getFirst().binding();
        List<String> run = new ArrayList<>();
        Core at = Core.withoutStanding(block.body());
        while (true) {
            switch (at) {
                case Core.Read read -> {
                    return read.binding().equals(element) ? run.reversed() : null;
                }
                case Core.FieldAccess access -> {
                    run.add(access.field());
                    at = Core.withoutStanding(access.target());
                }
                case Core.FieldProjection projection -> {
                    run.addAll(projection.steps().inOrder().reversed().stream()
                            .map(Core.FieldProjection.Step::field).toList());
                    at = Core.withoutStanding(projection.base());
                }
                default -> {
                    return null;
                }
            }
        }
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
