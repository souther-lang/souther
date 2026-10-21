package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.OneOfEach.Step;
import souther.compiler.partition.OneOfEach.Vocabulary;
import souther.compiler.partition.OneOfEach.Walked;
import souther.compiler.partition.OneOfEach.Way;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

/**
 * The ways a row takes through a count of statements ({@link OnTheWay.Counted}): which of the
 * statements hold, each as the entries it asks on the side it comes out.
 *
 * <p><b>Found where they are asked for, and never written out first.</b> Written out, a count is
 * every set of statements that comes to a count it admits, and its denial every set that does not:
 * most of the sets there are. Here the statements are taken in order, each holding and then
 * failing, and a side is taken only where the statements after it can still bring the count to one
 * admitted — so every step of the search is on the way to an assignment, and a way that holds
 * together is found after as many steps as there are statements.
 *
 * <p>Whether an assignment holds together with what is on the way is the vocabulary's to say, as it
 * says it of any entry ({@link Vocabulary#with}); a side taken in closes the assignment with the
 * reason it gives. Nothing is closed that was not shown closed: a choice of several ways inside a
 * statement, and a count inside one, are left for the walk of the assignment to choose.
 *
 * <p><b>Three answers, and a figure that is only ever the third.</b> The search finds assignments
 * ({@link Found.Some}), proves there are none and says why ({@link Found.None}), or runs past a
 * figure and proves nothing ({@link Found.Unknown}). A count the weights alone settle is no count
 * of statements ({@link OnTheWay.Counted}), so a search with no assignment and nothing to say why
 * is the third answer and never the second.
 *
 * <p><b>One figure for everything a way's count costs.</b> The steps are taken from one
 * {@link Steps} for the search, the walks of the assignments and every count in them, so the work
 * is bounded by the figure however the counts and choices on a way nest.
 */
final class CountedWays {

    private CountedWays() {
    }

    /**
     * What is left of the steps something may take, shared by everything that is asked of one
     * way. Taken from and never given back; once it has run out it says so for good.
     */
    static final class Steps {

        private int left;
        private boolean past;

        Steps(int most) {
            this.left = most;
        }

        /** The steps a whole way's counts may take together. */
        static Steps ofAWay() {
            return new Steps(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum());
        }

        /** The steps a single probe of whether a count can hold may take: no more than its share
         *  of what a way's counts take, since the walk asks it once for each way it chooses. */
        static Steps ofAProbe() {
            return new Steps(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum()
                    / CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum());
        }

        private boolean take() {
            if (left <= 0) {
                past = true;
                return false;
            }
            left--;
            return true;
        }

        /** Whether something asked for a step there was none of. */
        boolean ranOut() {
            return past;
        }
    }

    /** What the search found. */
    sealed interface Found<R> {

        /**
         * Assignments that hold together, one or more.
         *
         * @param assignments the entries of each assignment, every statement on the side it came
         *                    out, in the order the statements are kept
         * @param stoppedBy   null where these are every assignment that holds together; otherwise
         *                    the figure that left the rest unlooked at or not handed on
         */
        record Some<R>(List<List<OnTheWay>> assignments, CompositionBudget stoppedBy)
                implements Found<R> {

            public Some {
                assignments = List.copyOf(assignments);
                if (assignments.isEmpty()) {
                    throw new IllegalArgumentException("assignments found are one or more");
                }
            }
        }

        /** Every assignment was looked at and none holds together, for {@code why}. */
        record None<R>(R why) implements Found<R> {

            public None {
                if (why == null) {
                    throw new IllegalArgumentException("none holds together for some reason");
                }
            }
        }

        /** Nothing is proved: {@code stoppedBy} ran out before an assignment was found or every
         *  one was looked at. */
        record Unknown<R>(CompositionBudget stoppedBy) implements Found<R> {

            public Unknown {
                if (stoppedBy == null) {
                    throw new IllegalArgumentException("what is not known was stopped by a figure");
                }
            }
        }
    }

    /**
     * {@code so} with the count {@code counted} taken in: held, or closed where no assignment of
     * its statements holds together with {@code so}. Held where that is not known.
     */
    static <S, R> Step<S, R> admits(Vocabulary<OnTheWay, S, R> asked, S so,
                                    OnTheWay.Counted counted) {
        return switch (of(asked, so, counted, 1, false, Steps.ofAProbe())) {
            case Found.None<R>(R why) -> new Step.Closed<>(why);
            case Found.Some<R> _, Found.Unknown<R> _ -> new Step.Held<>(so);
        };
    }

    /**
     * The first {@code most} assignments of {@code counted} that hold together with {@code so},
     * taking their steps from {@code steps}.
     *
     * @param knowMore whether to look for one past {@code most}, to say whether there are more
     */
    static <S, R> Found<R> of(Vocabulary<OnTheWay, S, R> asked, S so, OnTheWay.Counted counted,
                              int most, boolean knowMore, Steps steps) {
        return new Search<>(new Metered<>(asked, steps), steps, counted,
                most + (knowMore ? 1 : 0)).run(so, most);
    }

    private static boolean settledNever(List<OnTheWay> side) {
        return side.stream().anyMatch(each ->
                each instanceof OnTheWay.Settled settled && !settled.thisWay());
    }

    /**
     * {@code asked}, taking in an entry only while there are steps: once there are none an entry
     * is held, which closes nothing, and the steps say so.
     */
    private record Metered<S, R>(Vocabulary<OnTheWay, S, R> asked, Steps steps)
            implements Vocabulary<OnTheWay, S, R> {

        @Override
        public List<List<OnTheWay>> alternatives(OnTheWay entry) {
            return asked.alternatives(entry);
        }

        @Override
        public Set<TermPath> positions(OnTheWay entry) {
            return asked.positions(entry);
        }

        @Override
        public S nothing() {
            return asked.nothing();
        }

        @Override
        public Step<S, R> with(S so, OnTheWay entry) {
            return steps.take() ? asked.with(so, entry) : new Step.Held<>(so);
        }
    }

    private static final class Search<S, R> {

        private final Vocabulary<OnTheWay, S, R> asked;
        private final Steps steps;
        private final List<OnTheWay.Counted.Statement> statements;
        private final boolean[] admitted;
        private final int limit;
        /** Whether the statements from each place on can come to each count more. */
        private final boolean[][] reach;
        private final boolean[] mayHold;
        private final boolean[] mayFail;
        private final List<List<OnTheWay>> found = new ArrayList<>();
        private R why;

        Search(Vocabulary<OnTheWay, S, R> asked, Steps steps, OnTheWay.Counted counted,
               int limit) {
            this.asked = asked;
            this.steps = steps;
            this.statements = counted.statements();
            this.limit = limit;
            int all = 0;
            for (OnTheWay.Counted.Statement each : statements) {
                all += each.weight();
            }
            admitted = new boolean[all + 1];
            counted.admitted().forEach(count -> admitted[count] = true);
            mayHold = new boolean[statements.size()];
            mayFail = new boolean[statements.size()];
            reach = new boolean[statements.size() + 1][all + 1];
            reach[statements.size()][0] = true;
            for (int at = statements.size() - 1; at >= 0; at--) {
                OnTheWay.Counted.Statement each = statements.get(at);
                mayHold[at] = !settledNever(each.holding());
                mayFail[at] = !settledNever(each.failing());
                for (int count = 0; count <= all; count++) {
                    reach[at][count] = (mayFail[at] && reach[at + 1][count])
                            || (mayHold[at] && count >= each.weight()
                                    && reach[at + 1][count - each.weight()]);
                }
            }
        }

        Found<R> run(S start, int most) {
            walk(0, 0, start, new ArrayList<>());
            if (!found.isEmpty()) {
                boolean more = found.size() > most;
                CompositionBudget stoppedBy = steps.ranOut()
                        ? CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT
                        : more ? CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG : null;
                return new Found.Some<>(more ? found.subList(0, most) : found, stoppedBy);
            }
            if (steps.ranOut()) {
                return new Found.Unknown<>(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
            }
            R because = why != null ? why : settledWhy(start);
            // Every assignment was looked at, and there is none. What closed them is the reason;
            // were there none, nothing is proved.
            return because != null ? new Found.None<>(because)
                    : new Found.Unknown<>(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
        }

        /** Why, where the counts the statements can come to leave none admitted, and so no side
         *  was taken in: a statement that never holds or never fails closes it. */
        private R settledWhy(S start) {
            for (OnTheWay.Counted.Statement each : statements) {
                for (List<OnTheWay> side : List.of(each.holding(), each.failing())) {
                    for (OnTheWay entry : side) {
                        if (entry instanceof OnTheWay.Settled settled && !settled.thisWay()
                                && asked.with(start, entry) instanceof Step.Closed<S, R>(R closed)) {
                            return closed;
                        }
                    }
                }
            }
            return null;
        }

        private boolean feasible(int from, int sum) {
            for (int count = sum; count < admitted.length; count++) {
                if (admitted[count] && reach[from][count - sum]) {
                    return true;
                }
            }
            return false;
        }

        private boolean done() {
            return steps.ranOut() || found.size() >= limit;
        }

        private void walk(int at, int sum, S so, List<OnTheWay> entries) {
            if (done()) {
                return;
            }
            if (at == statements.size()) {
                if (admitted[sum]) {
                    found.add(List.copyOf(entries));
                }
                return;
            }
            OnTheWay.Counted.Statement statement = statements.get(at);
            for (boolean holds : new boolean[] {true, false}) {
                if (done()) {
                    return;
                }
                int next = sum + (holds ? statement.weight() : 0);
                if (!(holds ? mayHold[at] : mayFail[at]) || !feasible(at + 1, next)) {
                    continue;
                }
                List<OnTheWay> side = holds ? statement.holding() : statement.failing();
                S here = so;
                boolean closed = false;
                for (OnTheWay entry : side) {
                    if (asked.alternatives(entry) != null || entry instanceof OnTheWay.Counted) {
                        continue;
                    }
                    switch (asked.with(here, entry)) {
                        case Step.Held<S, R>(S held) -> here = held;
                        case Step.Closed<S, R>(R because) -> {
                            if (why == null) {
                                why = because;
                            }
                            closed = true;
                        }
                    }
                    // An entry taken in with no step left closes nothing, and an assignment built
                    // on it is not one that was shown to hold together.
                    if (closed || steps.ranOut()) {
                        break;
                    }
                }
                if (!closed && !steps.ranOut()) {
                    int size = entries.size();
                    entries.addAll(side);
                    walk(at + 1, next, here, entries);
                    entries.subList(size, entries.size()).clear();
                }
            }
        }
    }

    /**
     * {@code walked}, with each count on a way it hands on replaced by the assignments of its
     * statements that hold together with the rest of the way — and closed where none does.
     *
     * <p>A way is judged whole here, as the walk judged only what it had taken in when it met the
     * count: the alternatives the walk chose after it are on the way now. The assignments are
     * walked again for the choices inside their statements, and are handed on as many as a way is
     * looked along; past them the figure is said, and no more is claimed.
     *
     * <p>The steps of the search for assignments and of every walk of them are taken from one
     * {@link Steps}, so that counts and choices nested in each other cost no more than a way's
     * figure together.
     *
     * @param again walks a list of entries as {@code walked} was walked, with the vocabulary it
     *              is given
     */
    static <S, R> Walked<OnTheWay, R> expanded(
            Walked<OnTheWay, R> walked, Vocabulary<OnTheWay, S, R> asked,
            BiFunction<List<OnTheWay>, Vocabulary<OnTheWay, S, R>, Walked<OnTheWay, R>> again) {
        if (!(walked instanceof Walked.Open<OnTheWay, R>(var ways, var stoppedBy))
                || ways.stream().noneMatch(CountedWays::holdsACount)) {
            return walked;
        }
        Expansion<S, R> out = new Expansion<>(asked, again, stoppedBy, Steps.ofAWay());
        ways.forEach(out::add);
        return out.result(entriesOf(ways.getFirst()));
    }

    private static boolean holdsACount(Way<OnTheWay> way) {
        return entriesOf(way).stream().anyMatch(OnTheWay.Counted.class::isInstance);
    }

    private static List<OnTheWay> entriesOf(Way<OnTheWay> way) {
        return switch (way) {
            case Way.Chosen<OnTheWay>(var entries, var _) -> entries;
            case Way.LeftUnchosen<OnTheWay>(var chosen, var _) -> chosen;
        };
    }

    private static final class Expansion<S, R> {

        private final Vocabulary<OnTheWay, S, R> asked;
        private final Vocabulary<OnTheWay, S, R> metered;
        private final BiFunction<List<OnTheWay>, Vocabulary<OnTheWay, S, R>,
                Walked<OnTheWay, R>> again;
        private final Steps steps;
        private final List<Way<OnTheWay>> ways = new ArrayList<>();
        private CompositionBudget stoppedBy;
        private R why;

        Expansion(Vocabulary<OnTheWay, S, R> asked,
                  BiFunction<List<OnTheWay>, Vocabulary<OnTheWay, S, R>,
                          Walked<OnTheWay, R>> again,
                  CompositionBudget stoppedBy, Steps steps) {
            this.asked = asked;
            this.metered = new Metered<>(asked, steps);
            this.again = again;
            this.stoppedBy = stoppedBy;
            this.steps = steps;
        }

        private void stoppedAt(CompositionBudget figure) {
            if (stoppedBy == null) {
                stoppedBy = figure;
            }
        }

        void add(Way<OnTheWay> way) {
            if (!holdsACount(way)) {
                keep(way);
            } else if (way instanceof Way.Chosen<OnTheWay>(var entries, var choices)
                    && !steps.ranOut()) {
                expand(way, entries, choices);
            } else {
                // A way that left choices unchosen is not walked again, and nor is one reached
                // with no step left: the figure is said, and the count stays on it for a composer
                // holding the statement whole.
                stoppedAt(steps.ranOut() ? CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT
                        : CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                keep(way);
            }
        }

        private void keep(Way<OnTheWay> way) {
            if (ways.size() == CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                stoppedAt(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                return;
            }
            ways.add(way);
        }

        private void expand(Way<OnTheWay> way, List<OnTheWay> entries,
                            List<OneOfEach.Choice<OnTheWay>> choices) {
            int at = 0;
            while (!(entries.get(at) instanceof OnTheWay.Counted)) {
                at++;
            }
            OnTheWay.Counted counted = (OnTheWay.Counted) entries.get(at);
            S so = metered.nothing();
            for (OnTheWay entry : entries) {
                if (entry instanceof OnTheWay.Counted || metered.alternatives(entry) != null) {
                    continue;
                }
                switch (metered.with(so, entry)) {
                    case Step.Held<S, R>(S held) -> so = held;
                    case Step.Closed<S, R>(R closed) -> {
                        closedBy(closed);
                        return;
                    }
                }
            }
            int room = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum() - ways.size();
            if (room <= 0) {
                stoppedAt(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                return;
            }
            switch (of(asked, so, counted, room, true, steps)) {
                case Found.None<R>(R closed) -> closedBy(closed);
                case Found.Unknown<R>(CompositionBudget figure) -> {
                    // Nothing was found and not everything was looked at: the count stays on the
                    // way.
                    stoppedAt(figure);
                    keep(way);
                }
                case Found.Some<R>(var assignments, var figure) -> {
                    if (figure != null) {
                        stoppedAt(figure);
                    }
                    for (List<OnTheWay> assignment : assignments) {
                        List<OnTheWay> replaced = new ArrayList<>(entries.subList(0, at));
                        replaced.addAll(assignment);
                        replaced.addAll(entries.subList(at + 1, entries.size()));
                        walkInto(replaced, choices);
                    }
                }
            }
        }

        /** The assignment {@code replaced}, walked for the choices inside its statements. */
        private void walkInto(List<OnTheWay> replaced, List<OneOfEach.Choice<OnTheWay>> choices) {
            switch (again.apply(replaced, metered)) {
                case Walked.Closed<OnTheWay, R>(var _, R closed) -> closedBy(closed);
                case Walked.Stopped<OnTheWay, R>(CompositionBudget figure) -> stoppedAt(figure);
                case Walked.Open<OnTheWay, R>(var more, var figure) -> {
                    if (figure != null) {
                        stoppedAt(figure);
                    }
                    for (Way<OnTheWay> one : more) {
                        addUnder(one, choices);
                    }
                }
            }
            if (steps.ranOut()) {
                stoppedAt(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
            }
        }

        /** {@code one}, a way the assignment was walked into, with the choices the way it came from
         *  made. */
        private void addUnder(Way<OnTheWay> one, List<OneOfEach.Choice<OnTheWay>> choices) {
            switch (one) {
                case Way.Chosen<OnTheWay>(var entries, var more) -> {
                    List<OneOfEach.Choice<OnTheWay>> both = new ArrayList<>(choices);
                    both.addAll(more);
                    Way<OnTheWay> made = new Way.Chosen<>(entries, both);
                    if (holdsACount(made) && !steps.ranOut()) {
                        expand(made, entries, both);
                    } else {
                        if (holdsACount(made)) {
                            stoppedAt(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
                        }
                        keep(made);
                    }
                }
                case Way.LeftUnchosen<OnTheWay> _ -> keep(one);
            }
        }

        private void closedBy(R closed) {
            if (why == null) {
                why = closed;
            }
        }

        Walked<OnTheWay, R> result(List<OnTheWay> firstWay) {
            if (!ways.isEmpty()) {
                return new Walked.Open<>(ways, stoppedBy);
            }
            if (stoppedBy != null) {
                return new Walked.Stopped<>(stoppedBy);
            }
            // Every way was closed, and something closed each. Were nothing said to, nothing is
            // proved.
            return why == null ? new Walked.Stopped<>(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT)
                    : new Walked.Closed<>(firstWay, why);
        }
    }
}
