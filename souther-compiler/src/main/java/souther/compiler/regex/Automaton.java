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

    /**
     * Either of them.
     *
     * <p>A new beginning that steps freely into both. Cheap: the states are the two machines'
     * together and one more, and nothing is copied.
     */
    Automaton or(Automaton other) {
        int mine = size();
        List<List<Step>> steps = new ArrayList<>();
        List<int[]> free = new ArrayList<>();
        steps.add(new ArrayList<>());
        free.add(new int[] {1, 1 + mine});
        shifted(this, 1, steps, free);
        shifted(other, 1 + mine, steps, free);
        BitSet accepting = new BitSet();
        shiftInto(accepting, this.accepting, 1);
        shiftInto(accepting, other.accepting, 1 + mine);
        return new Automaton(steps, free, accepting);
    }

    /**
     * Both of them, as the pairs of states a walk is in at once.
     *
     * <p>A step is taken where both machines have one over the same symbols, and what it is over is
     * what the two labels share — so the symbols neither has in common carry the pair nowhere, which
     * is what a conjunction says.
     *
     * <p>The free steps are each machine's own, taken one side at a time. A pair where one side
     * moves for nothing is the same pair with that side further on, which is exactly what a step
     * costing no symbol means.
     *
     * <p>The states are the product, and nothing here says whether that is a price worth paying:
     * both sizes are known before this is called, so a caller that has to answer for its work asks
     * them rather than being told afterwards.
     */
    Automaton and(Automaton other) {
        int wide = other.size();
        int count = size() * wide;
        List<List<Step>> steps = new ArrayList<>(count);
        List<int[]> free = new ArrayList<>(count);
        for (int i = 0; i < count; i++) {
            steps.add(new ArrayList<>());
            free.add(null);
        }
        for (int mine = 0; mine < size(); mine++) {
            for (int theirs = 0; theirs < wide; theirs++) {
                int pair = mine * wide + theirs;
                for (Step one : this.steps.get(mine)) {
                    for (Step two : other.steps.get(theirs)) {
                        CodePoints over = one.over().and(two.over());
                        if (!over.isEmpty()) {
                            steps.get(pair).add(new Step(over, one.to() * wide + two.to()));
                        }
                    }
                }
                List<Integer> freely = new ArrayList<>();
                for (int to : this.free.get(mine)) {
                    freely.add(to * wide + theirs);
                }
                for (int to : other.free.get(theirs)) {
                    freely.add(mine * wide + to);
                }
                int[] out = new int[freely.size()];
                for (int i = 0; i < out.length; i++) {
                    out[i] = freely.get(i);
                }
                free.set(pair, out);
            }
        }
        BitSet accepting = new BitSet();
        for (int mine = this.accepting.nextSetBit(0); mine >= 0;
                mine = this.accepting.nextSetBit(mine + 1)) {
            for (int theirs = other.accepting.nextSetBit(0); theirs >= 0;
                    theirs = other.accepting.nextSetBit(theirs + 1)) {
                accepting.set(mine * wide + theirs);
            }
        }
        return new Automaton(steps, free, accepting);
    }

    /**
     * Everything it does not accept.
     *
     * <p>The one operation that has to make the machine deterministic first, because what a walk
     * ends in has to be one answer before the answer can be turned over. Which is why it is here and
     * not underneath everything else: emptiness and acceptance never need it, and a caller wanting
     * to know whether a language is everything asks {@link #isEverything}, which stops at the first
     * string it finds outside.
     */
    Automaton not() {
        Subsets subsets = new Subsets();
        List<List<Step>> steps = new ArrayList<>();
        List<int[]> free = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int at = 0; at < subsets.count(); at++) {
            steps.add(new ArrayList<>());
            free.add(new int[0]);
            if (!subsets.acceptingAt(at)) {
                accepting.set(at);
            }
            for (Subsets.Move each : subsets.movesFrom(at)) {
                steps.get(at).add(new Step(each.over(), each.to()));
            }
        }
        return new Automaton(steps, free, accepting);
    }

    /** Whether it accepts nothing at all. */
    boolean isEmpty() {
        BitSet seen = closure(only(START));
        BitSet frontier = seen;
        while (!frontier.isEmpty()) {
            if (frontier.intersects(accepting)) {
                return false;
            }
            BitSet next = new BitSet();
            for (int state = frontier.nextSetBit(0); state >= 0;
                    state = frontier.nextSetBit(state + 1)) {
                for (Step each : steps.get(state)) {
                    if (!each.over().isEmpty()) {
                        next.set(each.to());
                    }
                }
            }
            next = closure(next);
            next.andNot(seen);
            seen.or(next);
            frontier = next;
        }
        // Every state a walk can be in has been in, and none of them is one it may stop at.
        return true;
    }

    /**
     * Whether it accepts every string there is.
     *
     * <p>Asked by walking the deterministic machine and stopping at the first place a walk could
     * end outside the language. A language that is not everything usually says so within a step or
     * two, and building the whole of the complement to ask the same question would pay for the worst
     * case every time.
     */
    boolean isEverything() {
        Subsets subsets = new Subsets();
        for (int at = 0; at < subsets.count(); at++) {
            if (!subsets.acceptingAt(at)) {
                return false;
            }
            // Grown as it is walked. A symbol leading nowhere leads to the subset of no states,
            // which accepts nothing — so the walk that ends outside the language is found by the
            // line above rather than by a case of its own.
            subsets.movesFrom(at);
        }
        return true;
    }

    /**
     * One string it accepts, or null where it accepts none.
     *
     * <p>Total wherever there is anything to answer with. Which is what ties it to
     * {@link #isEmpty}: a language that holds something and hands back nothing would be one whose
     * emptiness two readers disagree about, and the one that produces values would be believed.
     *
     * <p>The shortest, and among the strings of that length one written out of symbols a source can
     * carry where there is one. Being writable is a preference and never a condition: it is about
     * what a person can paste back, and a language holds what it holds. So the length is settled
     * first, over every symbol there is, and only then is a string of that length looked for among
     * the symbols that can be written.
     *
     * <p>Deterministic under both: the symbol taken out of a set is the least of it, and the states
     * are walked in the order they were made. Two runs over one model produce one value.
     */
    String shortest() {
        String any = shortest(CodePoints.EVERYTHING, -1);
        if (any == null) {
            return null;
        }
        // The length first, over every symbol there is, and only then a string of that length out
        // of the ones a source can carry. Asked the other way round, a language holding a control
        // character and a longer word of letters answers with the longer one — which is reaching
        // for what can be written at the price of what was asked for.
        String written = shortest(WRITABLE, any.codePointCount(0, any.length()));
        return written != null ? written : any;
    }

    /**
     * The symbols a value can be written out of and read back.
     *
     * <p>A control character other than the three a literal spells reaches a source as itself, and
     * half of a pair has nothing to be encoded as — so what a person pastes is not what was chosen.
     * Nothing about the language: a rule admitting one of these admits it, and this is only which of
     * them a value is preferably built from.
     */
    private static final CodePoints WRITABLE = CodePoints.EVERYTHING
            .less(CodePoints.between(0, 8))
            .less(CodePoints.between(0x0B, 0x0C))
            .less(CodePoints.between(0x0E, 0x1F))
            .less(CodePoints.of(0x7F))
            .less(CodePoints.between(0xD800, 0xDFFF));

    /**
     * The shortest string it accepts out of {@code these} and no longer than {@code mostSymbols},
     * or null where there is none. A length of {@code -1} is no bound at all.
     *
     * <p>Walked a length at a time, so the first accepting state met is met by a shortest string.
     * A state is kept the first time it is reached and not again: another way to the same state is
     * no shorter, and what follows it is the same either way.
     */
    private String shortest(CodePoints these, int mostSymbols) {
        java.util.Map<Integer, String> reached = new java.util.LinkedHashMap<>();
        BitSet seen = closure(only(START));
        for (int state = seen.nextSetBit(0); state >= 0; state = seen.nextSetBit(state + 1)) {
            reached.put(state, "");
        }
        int walked = 0;
        while (!reached.isEmpty()) {
            for (java.util.Map.Entry<Integer, String> each : reached.entrySet()) {
                if (accepting.get(each.getKey())) {
                    return each.getValue();
                }
            }
            if (mostSymbols >= 0 && walked == mostSymbols) {
                return null;
            }
            walked++;
            java.util.Map<Integer, String> next = new java.util.LinkedHashMap<>();
            for (java.util.Map.Entry<Integer, String> each : reached.entrySet()) {
                for (Step step : steps.get(each.getKey())) {
                    CodePoints over = step.over().and(these);
                    if (over.isEmpty()) {
                        continue;
                    }
                    String said = each.getValue() + new String(Character.toChars(over.least()));
                    BitSet after = closure(only(step.to()));
                    for (int state = after.nextSetBit(0); state >= 0;
                            state = after.nextSetBit(state + 1)) {
                        next.putIfAbsent(state, said);
                    }
                }
            }
            // Every state met at any shorter length is one nothing longer improves on, so a walk
            // that came back to one has nothing left to find down that way. Held over the whole
            // walk and not over the step before it: a state first met three symbols ago is no less
            // met for the step between.
            next.keySet().removeIf(seen::get);
            if (next.isEmpty()) {
                return null;
            }
            next.keySet().forEach(seen::set);
            reached = next;
        }
        return null;
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

    /** The same machine with every state moved up by {@code by}, written into what is being built. */
    private static void shifted(Automaton machine, int by,
                                List<List<Step>> steps, List<int[]> free) {
        for (int state = 0; state < machine.size(); state++) {
            List<Step> mine = new ArrayList<>();
            for (Step each : machine.steps.get(state)) {
                mine.add(new Step(each.over(), each.to() + by));
            }
            steps.add(mine);
            int[] theirs = machine.free.get(state);
            int[] moved = new int[theirs.length];
            for (int i = 0; i < theirs.length; i++) {
                moved[i] = theirs[i] + by;
            }
            free.add(moved);
        }
    }

    private static void shiftInto(BitSet out, BitSet from, int by) {
        for (int each = from.nextSetBit(0); each >= 0; each = from.nextSetBit(each + 1)) {
            out.set(each + by);
        }
    }

    /**
     * The machine read as one where a walk is only ever in one state, made as it is asked for.
     *
     * <p>Every question that needs a walk's end to be one answer comes through here: what a language
     * leaves out, and whether it leaves anything out. Grown a subset at a time, because both of them
     * usually have their answer within a step or two and the whole of a deterministic machine is
     * what the worst case costs.
     *
     * <p><b>Complete, the subset of no states among them.</b> A symbol with nowhere to go is a walk
     * that ends outside the language, and a machine that simply had no step there would leave every
     * reader to remember what a missing step means.
     *
     * <p>What a step is over is worked out once. The labels of a machine cut the symbols into runs
     * none of which any label splits, so one symbol out of each run answers for the whole of it —
     * and a deterministic machine over a million symbols has as many steps as the pattern has
     * distinct classes.
     */
    private final class Subsets {

        private final List<CodePoints> alphabet = new ArrayList<>();
        private final List<BitSet> subsets = new ArrayList<>();
        private final java.util.Map<BitSet, Integer> known = new java.util.HashMap<>();
        private final List<List<Move>> moves = new ArrayList<>();

        /** One step of the deterministic machine. */
        record Move(CodePoints over, int to) {}

        Subsets() {
            cutTheAlphabet();
            at(closure(only(START)));
        }

        int count() {
            return subsets.size();
        }

        boolean acceptingAt(int state) {
            return subsets.get(state).intersects(accepting);
        }

        /** The steps out of {@code state}, worked out the first time they are asked for. */
        List<Move> movesFrom(int state) {
            List<Move> said = moves.get(state);
            if (said != null) {
                return said;
            }
            List<Move> out = new ArrayList<>();
            BitSet here = subsets.get(state);
            for (CodePoints run : alphabet) {
                int symbol = run.least();
                BitSet next = new BitSet();
                for (int one = here.nextSetBit(0); one >= 0; one = here.nextSetBit(one + 1)) {
                    for (Step each : steps.get(one)) {
                        if (each.over().has(symbol)) {
                            next.set(each.to());
                        }
                    }
                }
                out.add(new Move(run, at(closure(next))));
            }
            moves.set(state, out);
            return out;
        }

        private int at(BitSet subset) {
            Integer had = known.get(subset);
            if (had != null) {
                return had;
            }
            int made = subsets.size();
            subsets.add(subset);
            moves.add(null);
            known.put(subset, made);
            return made;
        }

        /**
         * The runs of symbols no label of this machine tells apart.
         *
         * <p>Cut at every place a label begins or ends. Inside a run every symbol is over exactly
         * the same steps, so one of them answers for all of them — which is what makes a
         * deterministic machine over the whole of Unicode a small thing.
         */
        private void cutTheAlphabet() {
            java.util.TreeSet<Integer> cuts = new java.util.TreeSet<>();
            cuts.add(0);
            for (List<Step> out : steps) {
                for (Step each : out) {
                    for (CodePoints.Range run : each.over().ranges()) {
                        cuts.add(run.from());
                        if (run.to() < CodePoints.LAST) {
                            cuts.add(run.to() + 1);
                        }
                    }
                }
            }
            List<Integer> starts = new ArrayList<>(cuts);
            for (int i = 0; i < starts.size(); i++) {
                int from = starts.get(i);
                int to = i + 1 < starts.size() ? starts.get(i + 1) - 1 : CodePoints.LAST;
                alphabet.add(CodePoints.between(from, to));
            }
        }
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
