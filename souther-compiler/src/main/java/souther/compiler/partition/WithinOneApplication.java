package souther.compiler.partition;

import souther.compiler.check.ClosureUses;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

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
 *                     around it that is not applied so, and which of its uses fall short — which is
 *                     what a reader would change for the fork to be read one application at a time
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
     * Each use of {@code block}, standing where {@code reads} are the names, that is not an
     * operation of the language applying it once to every element of a container that is a
     * position of the input — none where every use is.
     *
     * <p>Every element and not some: an operation that stops at an answer is made on an element
     * only where what it answered on the ones before let it go on, and one that picks an element
     * out picks it by something else it was handed — decisions the way inside does not write. And a
     * container that is a position and not one made of it: the elements of a filter's answer are
     * the ones its closure let through, which is a decision on the way to every application
     * nothing inside writes either.
     *
     * <p>Read off the uses ({@link ClosureUses}) and nothing else, so that what is judged and what a
     * report says of it are one reading: the uses that fall short are both why the closure is read
     * as a whole and what the reason names.
     *
     * @param module the module whose body this is, whose author's words an operation is said in
     * @param said   an operation as that author would write it
     */
    static List<WhyKept.Shortfall> shortOfEachElement(Core.Block block, InputReads reads,
                                                     InputReading read, String module,
                                                     Function<ValueName, String> said) {
        ClosureUses uses = reads.usesOf(block);
        if (uses == null || uses.applications().isEmpty()) {
            return List.of(new WhyKept.Shortfall.NotOnlyByOperations());
        }
        Set<WhyKept.Shortfall> out = new LinkedHashSet<>();
        if (uses.usedElsewhere()) {
            out.add(new WhyKept.Shortfall.NotOnlyByOperations());
        }
        for (ClosureUses.Application each : uses.applications()) {
            if (each.applied() != HowAClosureIsApplied.TO_EVERY_ELEMENT) {
                out.add(new WhyKept.Shortfall.ToSomeOfTheElements(
                        asWritten(each, module, said), each.applied()));
            }
            Denotation container = new Denotation(each.container(), reads);
            if (!(container.at().pathOf(container.value(), read.newtypes())
                    instanceof PathResolution.At)) {
                out.add(new WhyKept.Shortfall.OverNoPosition(asWritten(each, module, said)));
            }
        }
        return List.copyOf(out);
    }

    /**
     * The operation {@code application} applies, as the author of {@code module} called it.
     *
     * <p>A call inside the body of a helper of another module, expanded where the author called
     * it, is one the author never wrote: what they called is the first helper the copy was expanded
     * from that is not one of {@code module}'s own, whose bodies the author wrote too.
     */
    private static String asWritten(ClosureUses.Application application, String module,
                                    Function<ValueName, String> said) {
        for (ValueName each : expandedFrom(application.lineage())) {
            if (!(each instanceof ValueName.Helper helper && helper.module().equals(module))) {
                return said.apply(each);
            }
        }
        return said.apply(application.operation());
    }

    /** What each copy {@code lineage} stands in was expanded from, the outermost first. */
    private static List<ValueName> expandedFrom(OccurrenceLineage lineage) {
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
        return new ArrayList<>(out);
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
        private final Deque<Optional<WhyKept.AFunctionReadAsAWhole>> around = new ArrayDeque<>();
        private final Set<ModelOccurrence> within = new LinkedHashSet<>();
        private final Set<ModelOccurrence> notWithin = new LinkedHashSet<>();
        private final Map<ModelOccurrence, WhyKept.AFunctionReadAsAWhole> readAsAWhole =
                new LinkedHashMap<>();

        /** That the walk goes into {@code block}, whose uses that are not an operation applying it
         *  once to each element of a position are {@code shortfalls}. */
        void entering(Core.Block block, List<WhyKept.Shortfall> shortfalls) {
            Optional<WhyKept.AFunctionReadAsAWhole> outer =
                    around.isEmpty() ? Optional.empty() : around.peek();
            around.push(outer.isPresent() || shortfalls.isEmpty() ? outer
                    : Optional.of(new WhyKept.AFunctionReadAsAWhole(block.pos(), shortfalls)));
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
            Optional<WhyKept.AFunctionReadAsAWhole> outermost = around.peek();
            if (outermost.isPresent()) {
                notWithin.add(fork);
                readAsAWhole.putIfAbsent(fork, outermost.get());
            } else {
                within.add(fork);
            }
        }

        WithinOneApplication read() {
            Set<ModelOccurrence> out = new LinkedHashSet<>(within);
            out.removeAll(notWithin);
            return new WithinOneApplication(out, readAsAWhole);
        }
    }
}
