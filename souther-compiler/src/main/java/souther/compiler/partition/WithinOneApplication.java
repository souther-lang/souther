package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * The forks a run gets to within one application of each closure around them, and under nothing
 * else the way there leaves unwritten.
 *
 * <p>A fork inside a closure is decided where something applies the closure, under whatever it is
 * applied to, and a way to it written from where the closure stands is written without that. Where
 * every closure around the fork is applied only by operations of the language, each applying it
 * once to every element of a container that is a position of the input, what the way was written
 * without is which element an application was handed: the element's position, which a decision on
 * the element is about already, and that the container holds it. Nothing else about the inputs —
 * whether an application is made at all is not what any other application answers, and an element
 * that is a position is not one some other decision let through.
 *
 * <p>What another application did reaches this one only through what the operation hands over
 * besides the element: what a walk carried from the step before. A decision on that is about no
 * position, and is read as one that may be about any of them wherever it is met; it is not this
 * answer's to account for.
 *
 * <p>Joined on the construct of the model the two readings agree about ({@link ModelOccurrence}). A
 * construct the walk met at two places, one of them not within one application, is not one.
 *
 * @param forks        the forks, each as the construct of the model it is
 * @param readAsAWhole for a fork inside a closure that is not one of them, the outermost closure
 *                     around it that is not applied so, which is what a reader would change for
 *                     the fork to be read one application at a time
 */
public record WithinOneApplication(Set<ModelOccurrence> forks,
                                   Map<ModelOccurrence, WhyKept.AFunctionReadAsAWhole>
                                           readAsAWhole) {

    public static final WithinOneApplication NONE = new WithinOneApplication(Set.of(), Map.of());

    public WithinOneApplication {
        forks = Set.copyOf(forks);
        readAsAWhole = Map.copyOf(readAsAWhole);
    }

    /** Whether a run gets to {@code fork}, in the tree that runs, within one application of each
     *  closure around it. */
    public boolean holdsAt(ConstructOccurrence fork) {
        return ModelOccurrence.statedAt(fork).map(forks::contains).orElse(false);
    }

    /** The closure around {@code fork} that keeps it from being got to within one application, where
     *  the walk met it inside one. */
    public Optional<WhyKept.AFunctionReadAsAWhole> readAsAWholeAt(ConstructOccurrence fork) {
        return ModelOccurrence.statedAt(fork).map(readAsAWhole::get);
    }

    /**
     * Whether {@code block}, standing where {@code reads} are the names, is applied only by
     * operations of the language, each applying it once to every element of a container that is a
     * position of the input.
     *
     * <p>Every element and not some: an operation that stops at an answer is made on an element
     * only where what it answered on the ones before let it go on, and one that picks an element
     * out picks it by something else it was handed — decisions the way inside does not write. And a
     * container that is a position and not one made of it: the elements of a filter's answer are
     * the ones its closure let through, which is a decision on the way to every application
     * nothing inside writes either.
     */
    static boolean eachElementOfAPosition(Core.Block block, InputReads reads, InputReading read) {
        List<InputReads.AppliedOver> over = reads.containersAppliedOver(block);
        List<HowAClosureIsApplied> how = reads.howItIsApplied(block);
        if (over.isEmpty() || how.isEmpty()
                || !how.stream().allMatch(HowAClosureIsApplied.TO_EVERY_ELEMENT::equals)) {
            return false;
        }
        for (InputReads.AppliedOver each : over) {
            Denotation container = each.container();
            if (!(container.at().pathOf(container.value(), read.newtypes())
                    instanceof PathResolution.At)) {
                return false;
            }
        }
        return true;
    }

    /**
     * What a walk finds as it meets the closures and the forks: each closure it goes into, whether
     * it is applied so, and each fork, under the closures it was met in.
     *
     * <p>The walk goes into a closure and out of it again in the order it meets them, so what the
     * closures around a fork are is the closures it is inside now.
     */
    static final class Gathered {

        /** For each closure the walk is inside, the innermost on top, the outermost of it and the
         *  ones around it that is not applied once to each element of a position by operations
         *  alone, or empty where none is. */
        private final Deque<Optional<Core.Block>> around = new ArrayDeque<>();
        /** What each closure is passed to, where a call of it was met. A closure given a name is
         *  met where the name is given, before the call it is passed to, so this is read once the
         *  walk is over. */
        private final Map<Core.Block, String> passedTo = new IdentityHashMap<>();
        /** The closure each {@code let} the walk met gave its name. */
        private final Map<BindingId, Core.Block> bound = new HashMap<>();
        private final Set<ModelOccurrence> within = new LinkedHashSet<>();
        private final Set<ModelOccurrence> notWithin = new LinkedHashSet<>();
        /** For each fork met inside a closure not applied so, the outermost such closure. */
        private final Map<ModelOccurrence, Core.Block> readAsAWhole = new LinkedHashMap<>();

        /** That the walk met {@code let}, which gives its name {@code block} where its value is a
         *  closure. */
        void binding(Core.LetIn let) {
            if (Core.withoutStanding(let.value()) instanceof Core.Block block) {
                bound.put(let.binder().binding(), block);
            }
        }

        /** The closure {@code arg} is: one written there, or one a {@code let} the walk met gave
         *  the name it reads. Null where it is neither. */
        private Core.Block closureOf(Core arg) {
            return switch (Core.withoutStanding(arg)) {
                case Core.Block block -> block;
                case Core.Read read -> bound.get(read.binding());
                default -> null;
            };
        }

        /**
         * That the walk met a call of {@code own} on {@code args}, in the copy {@code lineage}
         * says, which passes it each closure among them.
         *
         * <p>What a closure is passed to is the call the author of {@code module} wrote. A call
         * inside the body of a helper of another module, expanded where the author called it, is
         * one the author never wrote: what they called is the first helper the copy was expanded
         * from that is not one of {@code module}'s own, whose bodies the author wrote too.
         *
         * <p>The name is worked out where a closure is among the arguments and nowhere else: this
         * is asked of every call the walk meets, and most pass no closure. And a name an argument
         * reads is looked up among the closures {@code let}s gave a name, and not followed through
         * the bindings: what is had here is a label for a report.
         */
        void passing(List<Core> args, Supplier<String> own, OccurrenceLineage lineage,
                     String module, Function<ValueName, String> said) {
            String operation = null;
            for (Core each : args) {
                Core.Block block = closureOf(each);
                if (block == null || passedTo.containsKey(block)) {
                    continue;
                }
                if (operation == null) {
                    operation = calledAs(own, lineage, module, said);
                }
                passedTo.put(block, operation);
            }
        }

        /** What the author called, {@code said} as they would write it. */
        private static String calledAs(Supplier<String> own, OccurrenceLineage lineage,
                                       String module, Function<ValueName, String> said) {
            for (ValueName each : expandedFrom(lineage)) {
                if (!(each instanceof ValueName.Helper helper && helper.module().equals(module))) {
                    return said.apply(each);
                }
            }
            return own.get();
        }

        /** What each copy {@code lineage} stands in was expanded from, the outermost first. */
        private static Deque<ValueName> expandedFrom(OccurrenceLineage lineage) {
            Deque<ValueName> out = new ArrayDeque<>();
            OccurrenceLineage at = lineage;
            while (!(at instanceof OccurrenceLineage.Original)) {
                switch (at) {
                    case OccurrenceLineage.Expansion copy -> {
                        out.push(copy.expanded());
                        at = copy.within();
                    }
                    case OccurrenceLineage.Materialisation build -> at = build.within();
                    case OccurrenceLineage.Original _ -> { }
                }
            }
            return out;
        }

        /** That the walk goes into {@code block}, applied once to each element of a position of the
         *  input by operations alone where {@code eachElement} says so. */
        void entering(Core.Block block, boolean eachElement) {
            Optional<Core.Block> outer = around.isEmpty() ? Optional.empty() : around.peek();
            around.push(outer.isPresent() || eachElement ? outer : Optional.of(block));
        }

        /** That the walk comes out of the closure it went into last. */
        void leaving() {
            around.pop();
        }

        /** That the walk met {@code fork} where it is now. */
        void fork(ModelOccurrence fork) {
            if (around.isEmpty()) {
                notWithin.add(fork);
                return;
            }
            Optional<Core.Block> outermost = around.peek();
            if (outermost.isPresent()) {
                notWithin.add(fork);
                readAsAWhole.putIfAbsent(fork, outermost.get());
            } else {
                within.add(fork);
            }
        }

        /**
         * What the walk found.
         *
         * <p>A closure written in code out of the author's sight is passed to nothing they wrote,
         * so it is said by where it is and not by what it is passed to.
         */
        WithinOneApplication read() {
            Set<ModelOccurrence> out = new LinkedHashSet<>(within);
            out.removeAll(notWithin);
            Map<ModelOccurrence, WhyKept.AFunctionReadAsAWhole> said = new LinkedHashMap<>();
            readAsAWhole.forEach((fork, block) -> said.put(fork,
                    new WhyKept.AFunctionReadAsAWhole(block.pos(),
                            Citation.of(block.pos()) instanceof Citation.Elsewhere
                                    ? Optional.empty()
                                    : Optional.ofNullable(passedTo.get(block)))));
            return new WithinOneApplication(out, said);
        }
    }
}
