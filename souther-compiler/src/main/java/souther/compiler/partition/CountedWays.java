package souther.compiler.partition;

import souther.compiler.partition.OneOfEach.Step;
import souther.compiler.partition.OneOfEach.Vocabulary;
import souther.compiler.partition.OneOfEach.Walked;
import souther.compiler.partition.OneOfEach.Way;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

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
 * statement, and a count inside one, are left for the walk of the assignment to choose, and a
 * search that runs past its figure says so and proves nothing.
 */
final class CountedWays {

    private CountedWays() {
    }

    /**
     * What the search found.
     *
     * @param assignments the entries of each assignment found, every statement on the side it
     *                    came out, in the order the statements are kept
     * @param stoppedBy   null where {@code assignments} are every assignment that holds together;
     *                    otherwise the figure that left the rest unlooked at or not handed on
     * @param why         why no assignment holds together, where none was found and every one was
     *                    looked at; otherwise null
     */
    record Found<R>(List<List<OnTheWay>> assignments, CompositionBudget stoppedBy, R why) {

        Found {
            assignments = List.copyOf(assignments);
        }

        /** Whether no assignment holds together, proved. */
        boolean none() {
            return assignments.isEmpty() && stoppedBy == null && why != null;
        }
    }

    /**
     * {@code so} with the count {@code counted} taken in: held, or closed where no assignment of
     * its statements holds together with {@code so}.
     */
    static <S, R> Step<S, R> admits(Vocabulary<OnTheWay, S, R> asked, S so,
                                    OnTheWay.Counted counted) {
        Found<R> found = of(asked, so, counted, 1, false);
        return found.none() ? new Step.Closed<>(found.why()) : new Step.Held<>(so);
    }

    /**
     * The first {@code most} assignments of {@code counted} that hold together with {@code so}.
     *
     * @param knowMore whether to look for one past {@code most}, to say whether there are more
     */
    static <S, R> Found<R> of(Vocabulary<OnTheWay, S, R> asked, S so, OnTheWay.Counted counted,
                              int most, boolean knowMore) {
        return new Search<>(asked, counted, most + (knowMore ? 1 : 0)).run(so, most);
    }

    private static boolean settledNever(List<OnTheWay> side) {
        return side.stream().anyMatch(each ->
                each instanceof OnTheWay.Settled settled && !settled.thisWay());
    }

    private static final class Search<S, R> {

        private final Vocabulary<OnTheWay, S, R> asked;
        private final List<OnTheWay.Counted.Statement> statements;
        private final boolean[] admitted;
        private final int limit;
        /** Whether the statements from each place on can come to each count more. */
        private final boolean[][] reach;
        private final boolean[] mayHold;
        private final boolean[] mayFail;
        private final List<List<OnTheWay>> found = new ArrayList<>();
        private int left = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum();
        private boolean past;
        private R why;

        Search(Vocabulary<OnTheWay, S, R> asked, OnTheWay.Counted counted, int limit) {
            this.asked = asked;
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
            CompositionBudget stoppedBy = past ? CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT : null;
            List<List<OnTheWay>> handed = found;
            if (found.size() > most) {
                handed = found.subList(0, most);
                stoppedBy = stoppedBy == null ? CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG
                        : stoppedBy;
            }
            R because = handed.isEmpty() && stoppedBy == null
                    ? (why != null ? why : settledWhy(start)) : null;
            return new Found<>(handed, stoppedBy, because);
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

        private void walk(int at, int sum, S so, List<OnTheWay> entries) {
            if (past || found.size() >= limit) {
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
                if (past || found.size() >= limit) {
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
                    if (left-- == 0) {
                        past = true;
                        return;
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
                    if (closed) {
                        break;
                    }
                }
                if (!closed) {
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
     * @param again walks a list of entries as {@code walked} was walked
     */
    static <S, R> Walked<OnTheWay, R> expanded(Walked<OnTheWay, R> walked,
                                              Vocabulary<OnTheWay, S, R> asked,
                                              Function<List<OnTheWay>, Walked<OnTheWay, R>> again) {
        if (!(walked instanceof Walked.Open<OnTheWay, R>(var ways, var stoppedBy))
                || ways.stream().noneMatch(CountedWays::holdsACount)) {
            return walked;
        }
        Expansion<S, R> out = new Expansion<>(asked, again, stoppedBy);
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
        private final Function<List<OnTheWay>, Walked<OnTheWay, R>> again;
        private final List<Way<OnTheWay>> ways = new ArrayList<>();
        private CompositionBudget stoppedBy;
        private R why;

        Expansion(Vocabulary<OnTheWay, S, R> asked,
                  Function<List<OnTheWay>, Walked<OnTheWay, R>> again, CompositionBudget stoppedBy) {
            this.asked = asked;
            this.again = again;
            this.stoppedBy = stoppedBy;
        }

        void add(Way<OnTheWay> way) {
            if (!holdsACount(way)) {
                keep(way);
            } else if (way instanceof Way.Chosen<OnTheWay>(var entries, var choices)) {
                expand(way, entries, choices);
            } else {
                // A way that left choices unchosen is not walked again: the figure that left them
                // is said, and the count stays on it for a composer holding the statement whole.
                keep(way);
            }
        }

        private void keep(Way<OnTheWay> way) {
            if (ways.size() == CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum()) {
                stoppedBy = stoppedBy == null ? CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG
                        : stoppedBy;
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
            S so = asked.nothing();
            for (OnTheWay entry : entries) {
                if (entry instanceof OnTheWay.Counted || asked.alternatives(entry) != null) {
                    continue;
                }
                switch (asked.with(so, entry)) {
                    case Step.Held<S, R>(S held) -> so = held;
                    case Step.Closed<S, R>(R closed) -> {
                        closedBy(closed);
                        return;
                    }
                }
            }
            int room = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum() - ways.size();
            if (room <= 0) {
                stoppedBy = stoppedBy == null ? CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG
                        : stoppedBy;
                return;
            }
            Found<R> found = of(asked, so, counted, room, true);
            if (found.stoppedBy() != null && stoppedBy == null) {
                stoppedBy = found.stoppedBy();
            }
            if (found.none()) {
                closedBy(found.why());
                return;
            }
            if (found.assignments().isEmpty()) {
                // Nothing was found and not everything was looked at: the count stays on the way.
                keep(way);
                return;
            }
            for (List<OnTheWay> assignment : found.assignments()) {
                List<OnTheWay> replaced = new ArrayList<>(entries.subList(0, at));
                replaced.addAll(assignment);
                replaced.addAll(entries.subList(at + 1, entries.size()));
                switch (again.apply(replaced)) {
                    case Walked.Closed<OnTheWay, R>(var _, R closed) -> closedBy(closed);
                    case Walked.Stopped<OnTheWay, R>(CompositionBudget figure) -> {
                        if (stoppedBy == null) {
                            stoppedBy = figure;
                        }
                    }
                    case Walked.Open<OnTheWay, R>(var more, var figure) -> {
                        if (figure != null && stoppedBy == null) {
                            stoppedBy = figure;
                        }
                        for (Way<OnTheWay> one : more) {
                            addUnder(one, choices);
                        }
                    }
                }
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
                    if (holdsACount(made)) {
                        expand(made, entries, both);
                    } else {
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
            return new Walked.Closed<>(firstWay, why);
        }
    }
}
