package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

/**
 * The strings a pattern accepts, as states to walk between.
 *
 * <p>An automaton with steps that cost no symbol. Which is what the shape of a pattern asks for: a
 * choice is a step into either arm, a repetition is a step back to where it started, and neither
 * spends anything. Built without them, every one of those is a copy of what is under it and a
 * pattern of a few dozen characters is a great many states.
 *
 * <p>What labels a step is a set of symbols and never one. A class is one step over the whole of
 * what it holds, so a step is as cheap for `[^a]` as for `a` — read as one step per symbol, a
 * negated class over the whole universe would be a million of them, which is the same language and
 * a table nobody can hold.
 *
 * <p>Nothing here is about how a pattern was written. Two patterns that accept the same strings may
 * come to different automata, and that is the point of the next questions being asked of this rather
 * than of the syntax: what a language holds is not what its author typed.
 */
final class Automaton {

    /**
     * Where a walk begins.
     *
     * <p>Always zero, and the construction depends on it: a machine is built by adding states to the
     * end, so the first one made is the one everything else hangs from.
     */
    static final int START = 0;

    /** For each state, the steps that cost a symbol. */
    private final List<List<Step>> steps;

    /** For each state, the steps that cost nothing. */
    private final List<int[]> free;

    /** The states a walk may stop at. */
    private final BitSet accepting;

    /** One step, and what it costs to take. */
    record Step(CodePoints over, int to) {}

    private Automaton(List<List<Step>> steps, List<int[]> free, BitSet accepting) {
        this.steps = steps;
        this.free = free;
        this.accepting = accepting;
    }

    /** How many states it has, which is what a caller bounding its work counts. */
    int size() {
        return steps.size();
    }

    /**
     * The machine for {@code syntax}, or null where building it would take more than
     * {@code mostStates}.
     *
     * <p>Null rather than a smaller machine. A repetition written large is a language with a great
     * many strings in it and no smaller machine accepts the same ones — so what a caller is told is
     * that this was not built, which is a fact about this compiler, and never that the pattern
     * accepts less than it does.
     *
     * <p>What to do about it is the caller's. Which is why the bound is an argument: whether a
     * pattern is worth this many states is a question about the answer being built, and nothing here
     * knows what that answer is for.
     */
    static Automaton of(PatternSyntax syntax, int mostStates) {
        Building building = new Building(mostStates);
        try {
            int start = building.state();
            int accept = building.build(syntax, start);
            BitSet accepting = new BitSet();
            accepting.set(accept);
            return new Automaton(building.frozenSteps(), building.frozenFree(), accepting);
        } catch (TooMany _) {
            return null;
        }
    }

    /**
     * Whether the whole of {@code value} is accepted.
     *
     * <p>Walked a symbol at a time, where a symbol is what the engine reads: a code point where the
     * string holds a well-formed pair, and half of one where it holds half. Read a unit at a time,
     * a pattern naming a character past the basic plane would want two steps for what the engine
     * takes in one.
     */
    boolean accepts(String value) {
        BitSet here = closure(only(START));
        int at = 0;
        while (at < value.length()) {
            int symbol = value.codePointAt(at);
            at += Character.charCount(symbol);
            BitSet next = new BitSet();
            for (int state = here.nextSetBit(0); state >= 0; state = here.nextSetBit(state + 1)) {
                for (Step each : steps.get(state)) {
                    if (each.over().has(symbol)) {
                        next.set(each.to());
                    }
                }
            }
            if (next.isEmpty()) {
                return false;
            }
            here = closure(next);
        }
        return here.intersects(accepting);
    }

    /** The states reachable from {@code from} without spending a symbol, those included. */
    private BitSet closure(BitSet from) {
        BitSet out = (BitSet) from.clone();
        int[] pending = new int[out.cardinality()];
        int count = 0;
        for (int each = out.nextSetBit(0); each >= 0; each = out.nextSetBit(each + 1)) {
            pending[count++] = each;
        }
        while (count > 0) {
            int state = pending[--count];
            for (int to : free.get(state)) {
                if (!out.get(to)) {
                    out.set(to);
                    if (count == pending.length) {
                        pending = java.util.Arrays.copyOf(pending, count * 2 + 1);
                    }
                    pending[count++] = to;
                }
            }
        }
        return out;
    }

    private static BitSet only(int state) {
        BitSet out = new BitSet();
        out.set(state);
        return out;
    }

    /** What a machine is while it is being made. */
    private static final class Building {

        private final int mostStates;
        private final List<List<Step>> steps = new ArrayList<>();
        private final List<List<Integer>> free = new ArrayList<>();

        Building(int mostStates) {
            this.mostStates = mostStates;
        }

        int state() {
            if (steps.size() >= mostStates) {
                throw new TooMany();
            }
            steps.add(new ArrayList<>());
            free.add(new ArrayList<>());
            return steps.size() - 1;
        }

        void step(int from, CodePoints over, int to) {
            steps.get(from).add(new Step(over, to));
        }

        void freely(int from, int to) {
            free.get(from).add(to);
        }

        /**
         * The states for {@code syntax}, walked into from {@code from}, and where it leaves off.
         *
         * <p>One entry and one exit apiece, which is what makes the shapes compose without any of
         * them knowing what it is inside. No {@code default}: a shape of syntax added and not built
         * stops the compile rather than being read as whichever arm is nearest.
         */
        int build(PatternSyntax syntax, int from) {
            return switch (syntax) {
                case PatternSyntax.Nothing _ -> from;
                case PatternSyntax.Symbols it -> {
                    int to = state();
                    step(from, it.held(), to);
                    yield to;
                }
                case PatternSyntax.InTurn it -> {
                    int at = from;
                    for (PatternSyntax each : it.parts()) {
                        at = build(each, at);
                    }
                    yield at;
                }
                case PatternSyntax.EitherOf it -> {
                    int out = state();
                    for (PatternSyntax each : it.arms()) {
                        int in = state();
                        freely(from, in);
                        freely(build(each, in), out);
                    }
                    yield out;
                }
                case PatternSyntax.Repeated it -> repeated(it, from);
            };
        }

        /**
         * A repetition, as the copies it is.
         *
         * <p>The floor is copies one after another; what is above it is copies each of which may be
         * stepped over. An unbounded ceiling is one more copy with a step back to where it began.
         *
         * <p>Written out rather than held as a count. What a machine walks is states, and a
         * repetition of a thing is that thing however many times — so the states are the cost of the
         * language, and the bound a caller passes is what says whether that cost is worth paying.
         */
        int repeated(PatternSyntax.Repeated it, int from) {
            int at = from;
            for (int i = 0; i < it.least(); i++) {
                at = build(it.what(), at);
            }
            if (it.unbounded()) {
                int loop = state();
                freely(at, loop);
                freely(build(it.what(), loop), loop);
                return loop;
            }
            int out = state();
            freely(at, out);
            for (int i = it.least(); i < it.most(); i++) {
                at = build(it.what(), at);
                freely(at, out);
            }
            return out;
        }

        List<List<Step>> frozenSteps() {
            List<List<Step>> out = new ArrayList<>(steps.size());
            steps.forEach(each -> out.add(List.copyOf(each)));
            return List.copyOf(out);
        }

        List<int[]> frozenFree() {
            List<int[]> out = new ArrayList<>(free.size());
            for (List<Integer> each : free) {
                int[] to = new int[each.size()];
                for (int i = 0; i < to.length; i++) {
                    to[i] = each.get(i);
                }
                out.add(to);
            }
            return List.copyOf(out);
        }
    }

    /** More states than the caller allowed, carried to the one place that answers for it. */
    private static final class TooMany extends RuntimeException {

        private static final long serialVersionUID = 1L;

        TooMany() {
            super(null, null, false, false);
        }
    }
}
