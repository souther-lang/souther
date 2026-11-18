package souther.compiler.query;

import souther.compiler.check.CheckSurface;
import souther.compiler.check.HelperGraph;
import souther.compiler.ast.Hir;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meaning.AHelperReadOnApplicationsAroundIt;
import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The helpers one behavior's lines are written in whose copies stand in more than one application
 * of a closure a call outside them makes ({@link AHelperReadOnApplicationsAroundIt}), with how many
 * of the lines read and of their points owed a search those copies make.
 *
 * <p><b>Asked of the lines as read, and before anything is searched for at them.</b> What it reads
 * is {@link Adequacy.Readings}, which is what the search for rows at the lines' points is handed,
 * and nothing that search makes. So what this says can be told to an author before the search
 * runs, and what it costs does not turn on how long the search takes. Which of those points a
 * search is in the end made at is the search's own answer and is not said here: a point no
 * account keeps is left unsearched there, and this counts what the lines owe.
 *
 * <p>A line not worked out is read as well, under the condition it was said in, and owes its
 * points; so it is among these, and what a report says of a helper at such a line is read off
 * this. Not off the line's cases: a case of one candidate is made of nothing the function
 * applied to the candidates did, and the applications are what the line was read on.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record HelpersReadOnApplicationsAroundThem(String name, String behavior)
        implements Key<List<HelpersReadOnApplicationsAroundThem.Told>> {

    /**
     * How many points the readings of one helper's copies owe a search before an author is told
     * of the helper ahead of it. Below it the search those copies make is small beside the rest of
     * a measurement, and a helper called inside a closure is the usual way to write a model.
     */
    public static final int POINTS_TOLD_OF_BEFORE_THE_SEARCH = 64;

    /**
     * One helper, and what its copies add to the lines read.
     *
     * @param named        the helper and the calls whose applications stand around its copies
     * @param readings     how many readings of lines written in it were read on those applications
     * @param points       how many points those readings owe a search
     * @param calledInside the helpers that call it, and the ones calling those, out to a behavior:
     *                     every call of the helper written inside one has to move into the
     *                     behavior's own body, since a helper cannot call a behavior
     */
    public record Told(AHelperReadOnApplicationsAroundIt named, int readings, int points,
                       List<ValueName.Helper> calledInside) {

        public Told {
            Objects.requireNonNull(named, "some helper");
            calledInside = List.copyOf(calledInside);
        }

        /** Whether its copies owe a search enough points to be told of before the search. */
        public boolean worthTellingBeforeTheSearch() {
            return points >= POINTS_TOLD_OF_BEFORE_THE_SEARCH;
        }
    }

    /**
     * One helper of one behavior worth telling of before the search.
     *
     * @param module   the module
     * @param behavior the behavior whose lines are written in it
     * @param told     the helper, and what its copies add to the lines read
     */
    public record Said(String module, String behavior, Told told) {

        public Said {
            Objects.requireNonNull(module, "some module");
            Objects.requireNonNull(behavior, "some behavior");
            Objects.requireNonNull(told, "some helper");
        }
    }

    /**
     * Every helper of every behavior of {@code compilation} whose copies owe a search enough
     * points to be told of before it ({@link Told#worthTellingBeforeTheSearch}), behavior by
     * behavior in the order they are declared. Asks nothing a search makes.
     */
    public static List<Said> worthTellingBeforeTheSearch(Compilation compilation) {
        List<Said> out = new ArrayList<>();
        for (String module : compilation.modules()) {
            CheckSurface surface =
                    compilation.db().ask(new Shapes.CheckSurface(module)).value();
            if (surface == null) {
                continue;
            }
            for (Hir.BehaviorDef behavior : surface.behaviors()) {
                List<Told> told = compilation.db()
                        .ask(new HelpersReadOnApplicationsAroundThem(module, behavior.name()))
                        .value();
                if (told != null) {
                    told.stream().filter(Told::worthTellingBeforeTheSearch)
                            .forEach(each -> out.add(new Said(module, behavior.name(), each)));
                }
            }
        }
        return List.copyOf(out);
    }

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<List<Told>> compute(Db db) {
        LineReadings read = db.ask(new Adequacy.Readings(name, behavior)).value();
        Bodies.Expanding.Of expanding =
                db.ask(new Bodies.Expanding(name, InliningPolicy.FULL)).value();
        if (read == null || expanding == null) {
            return Answer.absent();
        }
        return Answer.of(told(read, expanding.graph()));
    }

    /** What the readings in {@code read} come to for each helper their lines are written in. */
    static List<Told> told(LineReadings read, HelperGraph graph) {
        Map<ValueName.Helper, Gathered> byHelper = new LinkedHashMap<>();
        for (BorderAssessment each : read.each()) {
            Optional<ValueName.Helper> writer = writerOf(each.readAt().inOrder());
            writer.ifPresent(helper -> byHelper.computeIfAbsent(helper, _ -> new Gathered())
                    .add(each));
        }
        List<Told> out = new ArrayList<>();
        byHelper.forEach((helper, gathered) -> gathered.named().ifPresent(named ->
                out.add(new Told(named, gathered.readings, gathered.points,
                        callersOf(graph, helper)))));
        return List.copyOf(out);
    }

    /** The one helper every copy in {@code copies} is written in, or empty where there is none. */
    private static Optional<ValueName.Helper> writerOf(List<ModelOccurrence> copies) {
        Set<Optional<ValueName.Helper>> writers = new LinkedHashSet<>();
        copies.forEach(copy -> writers.add(AHelperReadOnApplicationsAroundIt.writtenIn(copy)));
        return writers.size() == 1 ? writers.iterator().next() : Optional.empty();
    }

    /** The readings of one helper's lines, gathered. */
    private static final class Gathered {

        private final Set<ModelOccurrence> copies = new LinkedHashSet<>();
        private final List<ApplicationsReadOn> readOn = new ArrayList<>();
        private int readings;
        private int points;

        void add(BorderAssessment reading) {
            copies.addAll(reading.readAt().inOrder());
            readOn.add(reading.readOn());
            readings++;
            for (ItemAssessment item : reading.items().values()) {
                if (item instanceof ItemAssessment.Owed owed && owed.worthSearching()) {
                    points++;
                }
            }
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
