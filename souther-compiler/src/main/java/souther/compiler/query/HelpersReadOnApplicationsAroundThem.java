package souther.compiler.query;

import souther.compiler.check.CheckSurface;
import souther.compiler.check.HelperGraph;
import souther.compiler.ast.Hir;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meaning.AHelperReadOnApplicationsAroundIt;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The helpers one behavior's comparisons are written in whose copies stand in more than one
 * application of a closure a call outside them makes ({@link AHelperReadOnApplicationsAroundIt}),
 * with how many times those comparisons are read.
 *
 * <p><b>Asked of where the comparisons stand, and before anything is read of them.</b> What it
 * reads is {@link Adequacy.ComparisonsRead}: which constructs of the body may state something, in
 * which copies and on which applications, from the one walk of the body that draws the lines,
 * with nothing read of what they state. Drawing the lines, asking where they decide and searching
 * their points come after that and are what measuring a body costs, so what this says is known
 * while the compile is still all that has been paid for.
 *
 * <p>Read again on every application, each comparison is a reading each line is drawn from, and
 * each line is asked where it decides; how many lines those readings come to is not said here,
 * since readings drawing one line at one place come to one, and telling which do is the drawing.
 *
 * <p>A line asked no further for the number of its cases stands where the walk met it all the
 * same; so what a report says of a helper at such a line is read off this. Not off the line's
 * cases: a case of one candidate is made of nothing the function applied to the candidates did.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record HelpersReadOnApplicationsAroundThem(String name, String behavior)
        implements Key<List<HelpersReadOnApplicationsAroundThem.Told>> {

    /**
     * One helper, and how often its comparisons are read.
     *
     * @param named        the helper and the calls whose applications stand around its copies
     * @param readings     how many times its comparisons are read: each once on each application
     *                     of the closures it stands in ({@link AComparisonRead#readings})
     * @param calledInside the helpers that call it, and the ones calling those, out to a behavior:
     *                     every call of the helper written inside one has to move into the
     *                     behavior's own body, since a helper cannot call a behavior
     */
    public record Told(AHelperReadOnApplicationsAroundIt named, int readings,
                       List<ValueName.Helper> calledInside) {

        public Told {
            Objects.requireNonNull(named, "some helper");
            calledInside = List.copyOf(calledInside);
        }
    }

    /**
     * One helper of one module, with how many times each behavior that reads its comparisons on
     * applications around it reads them.
     *
     * <p>One per helper and not one per behavior: what an author does about it is declare the
     * helper, once, and every behavior reading it is told of together.
     *
     * @param module       the module
     * @param helper       the helper
     * @param readings     for each behavior that reads its comparisons so, how many times, in the
     *                     order the behaviors are declared
     * @param calledInside the helpers that call it, and the ones calling those, out to a behavior
     */
    public record Said(String module, ValueName.Helper helper, Map<String, Integer> readings,
                       List<ValueName.Helper> calledInside) {

        public Said {
            Objects.requireNonNull(module, "some module");
            Objects.requireNonNull(helper, "some helper");
            readings = Collections.unmodifiableMap(new LinkedHashMap<>(readings));
            calledInside = List.copyOf(calledInside);
            if (readings.isEmpty()) {
                throw new IllegalArgumentException("a helper is told of where some behavior"
                        + " reads it");
            }
        }
    }

    /**
     * Every helper of the behaviors {@code module} and {@code behavior} select whose comparisons
     * are read on applications of a function outside it ({@link AHelperReadOnApplicationsAroundIt}),
     * by module and helper, in the order the modules and behaviors are declared; a null selects
     * every one. Asks where the selected behaviors' comparisons stand and nothing about any other
     * behavior, and nothing the measurement makes.
     *
     * <p>Every such helper, however few times it is read. How much a reading costs is the
     * measurement's to find out, and what this says is where the readings come from: a figure
     * below which a helper went untold would be a reckoning of cost that nothing here makes.
     */
    public static List<Said> toldOf(Compilation compilation, String module, String behavior) {
        List<Said> out = new ArrayList<>();
        for (String name : compilation.modules()) {
            if (module != null && !module.equals(name)) {
                continue;
            }
            CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface(name)).value();
            if (surface == null) {
                continue;
            }
            Map<ValueName.Helper, Map<String, Integer>> readings = new LinkedHashMap<>();
            Map<ValueName.Helper, List<ValueName.Helper>> callers = new LinkedHashMap<>();
            for (Hir.BehaviorDef declared : surface.behaviors()) {
                if (behavior != null && !behavior.equals(declared.name())) {
                    continue;
                }
                List<Told> told = compilation.db()
                        .ask(new HelpersReadOnApplicationsAroundThem(name, declared.name()))
                        .value();
                if (told == null) {
                    continue;
                }
                for (Told each : told) {
                    ValueName.Helper helper = each.named().helper();
                    readings.computeIfAbsent(helper, _ -> new LinkedHashMap<>())
                            .put(declared.name(), each.readings());
                    callers.putIfAbsent(helper, each.calledInside());
                }
            }
            readings.forEach((helper, byBehavior) ->
                    out.add(new Said(name, helper, byBehavior, callers.get(helper))));
        }
        return List.copyOf(out);
    }

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<List<Told>> compute(Db db) {
        List<AComparisonRead> read = db.ask(new Adequacy.ComparisonsRead(name, behavior)).value();
        Bodies.Expanding.Of expanding =
                db.ask(new Bodies.Expanding(name, InliningPolicy.FULL)).value();
        if (read == null || expanding == null) {
            return Answer.absent();
        }
        return Answer.of(told(read, expanding.graph()));
    }

    /** What the comparisons in {@code read} come to for each helper they are written in. */
    static List<Told> told(List<AComparisonRead> read, HelperGraph graph) {
        Map<ValueName.Helper, Gathered> byHelper = new LinkedHashMap<>();
        for (AComparisonRead each : read) {
            AHelperReadOnApplicationsAroundIt.writtenIn(each.copy()).ifPresent(helper ->
                    byHelper.computeIfAbsent(helper, _ -> new Gathered()).add(each));
        }
        List<Told> out = new ArrayList<>();
        byHelper.forEach((helper, gathered) -> gathered.named().ifPresent(named ->
                out.add(new Told(named, gathered.readings, callersOf(graph, helper)))));
        return List.copyOf(out);
    }

    /** The comparisons of one helper, gathered. */
    private static final class Gathered {

        private final Set<ModelOccurrence> copies = new LinkedHashSet<>();
        private final List<ApplicationsReadOn> readOn = new ArrayList<>();
        private int readings;

        void add(AComparisonRead comparison) {
            copies.add(comparison.copy());
            readOn.addAll(comparison.applications());
            readings += comparison.readings();
        }

        Optional<AHelperReadOnApplicationsAroundIt> named() {
            List<AHelperReadOnApplicationsAroundIt.Applied> applied = new ArrayList<>();
            for (ApplicationsReadOn.OfACall call : ApplicationsReadOn.byCall(readOn)) {
                applied.add(new AHelperReadOnApplicationsAroundIt.Applied(call.construct(),
                        call.applications()));
            }
            return AHelperReadOnApplicationsAroundIt.of(copies, applied);
        }
    }

    /**
     * The helpers that call {@code helper}, and those that call them, each once, the nearest
     * first, in the order the graph holds them.
     */
    public static List<ValueName.Helper> callersOf(HelperGraph graph, ValueName.Helper helper) {
        Set<ValueName.Helper> out = new LinkedHashSet<>();
        Deque<ValueName.Helper> work = new ArrayDeque<>(List.of(helper));
        while (!work.isEmpty()) {
            ValueName.Helper called = work.poll();
            for (Map.Entry<ReachName.Declaration, Set<ReachName.Declaration>> each
                    : graph.callsOf().entrySet()) {
                if (each.getKey().denotes() instanceof ValueName.Helper caller
                        && !caller.equals(helper)
                        && each.getValue().stream().anyMatch(
                                callee -> callee.denotes().equals(called))
                        && out.add(caller)) {
                    work.add(caller);
                }
            }
        }
        return List.copyOf(out);
    }
}
