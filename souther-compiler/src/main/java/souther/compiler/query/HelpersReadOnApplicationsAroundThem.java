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
 * with how many applications those copies stand on.
 *
 * <p><b>Asked of where the comparisons stand, and before anything is read of them.</b> What it
 * reads is {@link Adequacy.ComparisonsRead}: which constructs of the body may state something, in
 * which copies and on which applications, from the one walk of the body that draws the lines,
 * with nothing read of what they state. Drawing the lines, asking where they decide and searching
 * their points come after that and are what measuring a body costs, so what this says is known
 * while the compile is still all that has been paid for.
 *
 * <p>So what it says is where the constructs stand, and no more. A construct met here may state
 * nothing a line is drawn from — a comparison whose statement is carried past it, an application
 * stating nothing of its own — and how many lines the applications it stands on come to is not
 * said either, since readings drawing one line at one place come to one, and telling which do is
 * the drawing.
 *
 * <p>A line asked no further for the number of its cases stands where the walk met it all the
 * same; so what a report says of a helper at such a line is read off this, of the copies the line
 * was read at alone ({@link AHelperReadOnApplicationsAroundIt#restrictedTo}). Not off the line's
 * cases: a case of one candidate is made of nothing the function applied to the candidates did.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record HelpersReadOnApplicationsAroundThem(String name, String behavior)
        implements Key<List<HelpersReadOnApplicationsAroundThem.Told>> {

    /**
     * One helper, the copies of its comparisons with the calls around each, and how many
     * applications those copies stand on.
     *
     * @param named        the helper, and each copy of its comparisons with a call outside it
     *                     that applies a closure around it more than once
     * @param applications how many applications those copies stand on together, each copy's as
     *                     the walk said them one by one
     * @param calledInside the helpers that call it, and the ones calling those, out to a behavior:
     *                     every call of the helper written inside one has to move into the
     *                     behavior's own body, since a helper cannot call a behavior
     */
    public record Told(AHelperReadOnApplicationsAroundIt named, int applications,
                       List<ValueName.Helper> calledInside) {

        public Told {
            Objects.requireNonNull(named, "some helper");
            calledInside = List.copyOf(calledInside);
        }
    }

    /**
     * One helper of one module, with how many applications of functions outside it its
     * comparisons stand on, in each behavior where they do.
     *
     * <p>One per helper and not one per behavior: what an author does about it is declare the
     * helper, once, and every behavior it stands so in is told of together.
     *
     * @param module       the module
     * @param helper       the helper
     * @param applications for each behavior its comparisons stand so in, on how many applications,
     *                     in the order the behaviors are declared
     * @param calledInside the helpers that call it, and the ones calling those, out to a behavior
     */
    public record Said(String module, ValueName.Helper helper, Map<String, Integer> applications,
                       List<ValueName.Helper> calledInside) {

        public Said {
            Objects.requireNonNull(module, "some module");
            Objects.requireNonNull(helper, "some helper");
            applications = Collections.unmodifiableMap(new LinkedHashMap<>(applications));
            calledInside = List.copyOf(calledInside);
            if (applications.isEmpty()) {
                throw new IllegalArgumentException("a helper is told of where it stands in some"
                        + " behavior");
            }
        }
    }

    /**
     * Every helper of the behaviors {@code module} and {@code behavior} select whose comparisons
     * stand on applications of a function outside it ({@link AHelperReadOnApplicationsAroundIt}),
     * by module and helper, in the order the modules and behaviors are declared; a null selects
     * every one. Asks where the selected behaviors' comparisons stand and nothing about any other
     * behavior, and nothing the measurement makes.
     *
     * <p>Every such helper, on however few applications. How much they cost is the measurement's
     * to find out, and what this says is where the comparisons stand: a figure below which a
     * helper went untold would be a reckoning of cost that nothing here makes.
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
            Map<ValueName.Helper, Map<String, Integer>> applications = new LinkedHashMap<>();
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
                    applications.computeIfAbsent(helper, _ -> new LinkedHashMap<>())
                            .put(declared.name(), each.applications());
                    callers.putIfAbsent(helper, each.calledInside());
                }
            }
            applications.forEach((helper, byBehavior) ->
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
                out.add(new Told(named, gathered.applicationsOf(named),
                        callersOf(graph, helper)))));
        return List.copyOf(out);
    }

    /** The comparisons of one helper, gathered. */
    private static final class Gathered {

        /** Each copy with a call around it, and how many of its applications the copy stands
         *  on, as the walk said them one by one. */
        private final List<AHelperReadOnApplicationsAroundIt.ReadAgain> read = new ArrayList<>();
        /** How many applications each copy stands on, by copy. */
        private final Map<ModelOccurrence, Integer> applications = new LinkedHashMap<>();

        /** {@code comparison}, where the walk said each application it stands on; one whose
         *  applications are not said, or that stands on none, has no call around it to tell. */
        void add(AComparisonRead comparison) {
            if (!(comparison.on() instanceof AComparisonRead.AppliedOn.OnEach(var each))) {
                return;
            }
            applications.merge(comparison.copy(), each.size(), Integer::sum);
            for (ApplicationsReadOn.OfACall call : ApplicationsReadOn.byCall(each)) {
                read.add(new AHelperReadOnApplicationsAroundIt.ReadAgain(comparison.copy(),
                        call.construct(), call.applications()));
            }
        }

        Optional<AHelperReadOnApplicationsAroundIt> named() {
            return AHelperReadOnApplicationsAroundIt.of(read);
        }

        /** How many applications the copies {@code named} tells of stand on, together. */
        int applicationsOf(AHelperReadOnApplicationsAroundIt named) {
            Set<ModelOccurrence> copies = new LinkedHashSet<>();
            named.around().forEach(each -> copies.add(each.copy()));
            return copies.stream().mapToInt(applications::get).sum();
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
