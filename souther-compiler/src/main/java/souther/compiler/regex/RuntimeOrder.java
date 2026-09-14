package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * The strings' own order, asked of a language.
 *
 * <p>{@link String#compareTo}, which is the comparison the runtime makes and the one a model's
 * {@code <} is (spec §primitives). It orders UTF-16 code units, and a symbol here is what a matcher
 * reads — a code point where a string holds a well-formed pair, a unit where it holds half of one
 * ({@link CodePoints}). Those are not the same order and no relabelling of the symbols makes them
 * one: {@code "\uD800￿"} is one unit above {@code "𐀀"} on the runtime's order and
 * one symbol below it here, because the two spend a different number of units on their first
 * symbol. So everything below reads a language a unit at a time, and the symbols are taken apart
 * where they are read.
 *
 * <p>Which is the whole of why this is a place rather than a comparator handed to a language. A
 * comparator can order two symbols and cannot say that one of them ends where the other has more to
 * come — and the answer to that is what the two questions here are about.
 *
 * <p><b>Answerable to the order itself.</b> Nothing here is a second definition of {@code <} on
 * strings: what is built is a machine and what is walked is a machine, and both are held to
 * {@code String.compareTo} by the laws over them
 * ({@code TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest}).
 */
final class RuntimeOrder {

    /** The greatest UTF-16 code unit, which is where a unit stops being one. */
    private static final int LAST_UNIT = 0xFFFF;

    private static final int HIGH_FROM = 0xD800;
    private static final int HIGH_TO = 0xDBFF;
    private static final int LOW_FROM = 0xDC00;
    private static final int LOW_TO = 0xDFFF;

    /** The first symbol past the units, which is where a pair's two units stand for one symbol. */
    private static final int PAIRED_FROM = 0x10000;

    /**
     * The machine accepting every string that comes before {@code than}, or null past what
     * {@code meter} allows.
     *
     * <p>One state per unit of {@code than} and two besides. A walk is at the state saying how many
     * of those units the string has matched exactly; a unit below the next one settles the answer
     * and a unit above it leads nowhere, so the states a walk can be in are that count, the state
     * where the whole of {@code than} has been matched, and the one where the answer is already
     * yes.
     *
     * <p>A walk that stops having matched some of {@code than} and no more is a string that is a
     * proper prefix of it, which is below it — so those states are where a walk may stop, and the
     * one that matched all of it is not, since that string is {@code than} itself.
     */
    static Automaton before(String than, Meter meter) {
        int units = than.length();
        Meter.Making making = meter.making();
        if (!making.states(units + 2L)) {
            return null;
        }
        int below = units + 1;
        List<List<Automaton.Step>> steps = new ArrayList<>();
        for (int at = 0; at <= below; at++) {
            steps.add(new ArrayList<>());
        }
        BitSet accepting = new BitSet();
        for (int at = 0; at < units; at++) {
            accepting.set(at);
            written(steps.get(at), than, at, below);
        }
        accepting.set(below);
        steps.get(below).add(new Automaton.Step(CodePoints.EVERYTHING, below));
        return Automaton.madeOf(steps, accepting);
    }

    /**
     * What one symbol read at {@code at} does, as the steps out of that state.
     *
     * <p>Two kinds of symbol and not one. A symbol below the units is a unit and is compared with
     * the one wanted here; a symbol above them is a pair, and its first unit is compared here while
     * its second is compared against the unit after — so a pair can settle the answer, carry the
     * walk two units on, or lead nowhere, and which of the three is read off both units together.
     */
    private static void written(List<Automaton.Step> out, String than, int at, int below) {
        char want = than.charAt(at);
        CodePoints lower = want > 0 ? CodePoints.between(0, want - 1) : CodePoints.NONE;
        lower = lower.or(pairsBefore(want));
        if (!lower.isEmpty()) {
            out.add(new Automaton.Step(lower, below));
        }
        out.add(new Automaton.Step(CodePoints.of(want), at + 1));
        pairAt(out, than, at, below);
    }

    /**
     * The pairs whose first unit is already below {@code want}.
     *
     * <p>A pair's first unit is a high surrogate, so which pairs these are turns on where
     * {@code want} sits against that range: above all of them every pair is below, below all of them
     * none is, and inside them it is the pairs written with a smaller high surrogate.
     */
    private static CodePoints pairsBefore(char want) {
        if (want > HIGH_TO) {
            return CodePoints.between(PAIRED_FROM, CodePoints.LAST);
        }
        if (want <= HIGH_FROM) {
            return CodePoints.NONE;
        }
        return CodePoints.between(PAIRED_FROM, blockOf(want) - 1);
    }

    /**
     * What a pair whose first unit is exactly the one wanted here comes to.
     *
     * <p>Its second unit is compared against the unit after this one. Where there is none —
     * {@code than} ends on the high surrogate — the string has all of {@code than} and goes on, so
     * it is above it and the pair leads nowhere.
     */
    private static void pairAt(List<Automaton.Step> out, String than, int at, int below) {
        char want = than.charAt(at);
        if (want < HIGH_FROM || want > HIGH_TO) {
            return;
        }
        int block = blockOf(want);
        if (at + 1 >= than.length()) {
            return;
        }
        char next = than.charAt(at + 1);
        if (next < LOW_FROM) {
            return;
        }
        if (next > LOW_TO) {
            out.add(new Automaton.Step(CodePoints.between(block, block + (LOW_TO - LOW_FROM)),
                    below));
            return;
        }
        int same = block + (next - LOW_FROM);
        if (same > block) {
            out.add(new Automaton.Step(CodePoints.between(block, same - 1), below));
        }
        out.add(new Automaton.Step(CodePoints.of(same), at + 2));
    }

    /** The first symbol written with {@code high} as its first unit. */
    private static int blockOf(int high) {
        return PAIRED_FROM + ((high - HIGH_FROM) << 10);
    }

    /**
     * The symbol sequences some string is read as, canonical and made once.
     *
     * <p>A constant and not a construction a caller pays for. It is three states whatever is asked
     * of it, and what it says is a fact about how a string is read rather than anything a model
     * wrote — charged to an allowance, every language would be a little smaller than the one before
     * it for a reason nobody could see.
     */
    static final Automaton EVERY_STRING = canonicalOnlyStrings();

    /**
     * The same machine as it is written, which is what a product is taken against.
     *
     * <p>Two states and not the canonical three. A machine is not required to be complete, so the
     * state a walk goes to when it is already refused need not be there — and a product is charged
     * for the states it will make, so leaving it out is a third off every restriction.
     */
    static final Automaton READS_ONLY_STRINGS = onlyStrings();

    private static Automaton onlyStrings() {
        Automaton made = everyString(new Meter(16, 64));
        if (made == null) {
            throw new IllegalStateException("the machine that reads only strings is two states");
        }
        return made;
    }

    private static Automaton canonicalOnlyStrings() {
        // Its own, and not the constant beside it. A constant made out of another is made after it
        // whatever a reader expects of the order they are written in, and one made first reads
        // nothing where the other will be.
        Meter meter = new Meter(16, 64);
        Automaton one = onlyStrings().canonical(meter);
        if (one == null) {
            throw new IllegalStateException("the machine for every string is three states");
        }
        return one;
    }

    /**
     * The symbol sequences some string is read as, or null past what {@code meter} allows.
     *
     * <p>Not every sequence of symbols is one. A high surrogate followed by a low one is the pair —
     * that is what a matcher reads and what a walk over a string takes in — so those two symbols
     * never stand beside each other, and a sequence holding them is one no string produces.
     *
     * <p>Which matters wherever a set question is asked rather than a membership one. Whether a
     * string is held is walked out of the string and never meets such a sequence; whether two
     * languages hold the same strings is a walk over two machines, and two machines telling the
     * same strings apart from each other only over sequences no string reads as are two spellings of
     * one set. So a reader taking a complement to ask about strings meets it with this, and a reader
     * asking whether a string is in something does not need it.
     */
    static Automaton everyString(Meter meter) {
        Meter.Making making = meter.making();
        if (!making.states(2)) {
            return null;
        }
        CodePoints high = CodePoints.between(HIGH_FROM, HIGH_TO);
        CodePoints low = CodePoints.between(LOW_FROM, LOW_TO);
        List<List<Automaton.Step>> steps = new ArrayList<>();
        steps.add(new ArrayList<>(List.of(
                new Automaton.Step(CodePoints.EVERYTHING.less(high), 0),
                new Automaton.Step(high, 1))));
        steps.add(new ArrayList<>(List.of(
                new Automaton.Step(CodePoints.EVERYTHING.less(high).less(low), 0),
                new Automaton.Step(high, 1))));
        BitSet accepting = new BitSet();
        accepting.set(0);
        accepting.set(1);
        return Automaton.madeOf(steps, accepting);
    }

    /**
     * The least string {@code machine} accepts, or null where it accepts none and where the ones it
     * accepts have no least among them.
     *
     * <p>Two answers under one null on purpose: neither is a place on the order, and a caller
     * wanting them apart asks whether the language holds anything, which is free. What has no least
     * is a language whose strings descend without stopping — {@code a*b} holds {@code b} above
     * {@code ab} above {@code aab} and so on down — and the greatest lower bound of those is not a
     * string. There is nothing to write down, and a reading that answered with the one it had
     * reached would be naming a value the rules do not stop at.
     *
     * <p>Free, as everything asked of a language is: the machine is in front of this and nothing is
     * built. A walk a unit at a time over a machine whose steps are symbols, which is why the states
     * are a set rather than one — a high surrogate is a symbol of its own and the first unit of
     * every pair, so a unit read here can leave the walk in both.
     *
     * <p><b>Asked of a machine that stops only on strings</b>, which every {@link Language} holds
     * ({@link Language#canonical}). So a walk that reads a high surrogate as a symbol of its own and
     * a low one after it — two symbols no string is read as — reaches nothing it may stop at, and
     * the least is a string the machine accepts. Asked of a machine that stops on such a sequence,
     * this would answer with it and the language would say it holds no such string.
     *
     * <p>Least by taking the least unit that still leads to somewhere a walk may stop, and stopping
     * at the first place it may. A shorter string is below every string it begins, so where the walk
     * may stop it has the least; and where it comes back to a set of states it has been in, it never
     * will — the same units are chosen again, and each time round leaves a string below the last.
     */
    static String leastOf(Automaton machine) {
        boolean[] reaches = machine.reachingSomewhereItStops();
        if (!reaches[Automaton.START]) {
            return null;
        }
        StringBuilder out = new StringBuilder();
        Set<Where> here = Set.of(new Where(Automaton.START, null));
        Set<Set<Where>> been = new LinkedHashSet<>();
        while (been.add(here)) {
            if (stops(here, machine)) {
                return out.toString();
            }
            int unit = leastUnit(here, machine, reaches);
            if (unit < 0) {
                return null;
            }
            out.append((char) unit);
            here = after(here, unit, machine);
        }
        return null;
    }

    /**
     * Where a walk is, which is a state of the machine or half way into a pair.
     *
     * @param state where the walk is, or where the pair being read leads
     * @param lows  the second units the pair may be finished with, or null where the walk is at a
     *              symbol boundary. A high surrogate read at a boundary is both a symbol and the
     *              first unit of a pair, so both are held and the walk is in as many places as the
     *              units so far leave it
     */
    private record Where(int state, CodePoints lows) {}

    /** Whether a walk in one of these may stop, which it may only at a symbol boundary. */
    private static boolean stops(Set<Where> here, Automaton machine) {
        return here.stream().anyMatch(each -> each.lows() == null && machine.stopsAt(each.state()));
    }

    /** Whether a walk in one of these may still reach somewhere it stops. */
    private static boolean reachable(Set<Where> here, boolean[] reaches) {
        return here.stream().anyMatch(each -> reaches[each.state()]);
    }

    /**
     * The least unit that leaves the walk somewhere it may still stop, or -1 where no unit does.
     *
     * <p>Over the units the steps change at rather than over every unit there is. What a step is
     * over is runs of symbols, so two units inside one run of every step here lead to the same
     * places — and the least of a run is the one to try.
     */
    private static int leastUnit(Set<Where> here, Automaton machine, boolean[] reaches) {
        for (int unit : boundaries(here, machine)) {
            if (reachable(after(here, unit, machine), reaches)) {
                return unit;
            }
        }
        return -1;
    }

    /** The units where what a step leads to can change, in order. */
    private static Set<Integer> boundaries(Set<Where> here, Automaton machine) {
        Set<Integer> out = new TreeSet<>();
        for (Where each : here) {
            if (each.lows() != null) {
                starts(out, each.lows());
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(each.state())) {
                starts(out, unitsOf(step.over()));
                starts(out, highsOf(step.over()));
            }
        }
        return out;
    }

    private static void starts(Set<Integer> out, CodePoints over) {
        for (CodePoints.Range each : over.ranges()) {
            out.add(each.from());
        }
    }

    /** Where the walk is once {@code unit} has been read. */
    private static Set<Where> after(Set<Where> here, int unit, Automaton machine) {
        Set<Where> out = new LinkedHashSet<>();
        for (Where each : here) {
            if (each.lows() != null) {
                if (each.lows().has(unit)) {
                    out.add(new Where(each.state(), null));
                }
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(each.state())) {
                if (unit <= LAST_UNIT && step.over().has(unit)) {
                    out.add(new Where(step.to(), null));
                }
                CodePoints lows = lowsOf(step.over(), unit);
                if (!lows.isEmpty()) {
                    out.add(new Where(step.to(), lows));
                }
            }
        }
        return out;
    }

    /** The symbols in {@code over} that are units, as those units. */
    private static CodePoints unitsOf(CodePoints over) {
        return over.and(CodePoints.between(0, LAST_UNIT));
    }

    /** The first units of the pairs in {@code over}. */
    private static CodePoints highsOf(CodePoints over) {
        List<CodePoints.Range> out = new ArrayList<>();
        for (CodePoints.Range each : over.ranges()) {
            int from = Math.max(each.from(), PAIRED_FROM);
            if (from > each.to()) {
                continue;
            }
            out.add(new CodePoints.Range(highOf(from), highOf(each.to())));
        }
        return new CodePoints(out);
    }

    /** The second units a pair beginning with {@code high} may be finished with, here. */
    private static CodePoints lowsOf(CodePoints over, int high) {
        if (high < HIGH_FROM || high > HIGH_TO) {
            return CodePoints.NONE;
        }
        int block = blockOf(high);
        CodePoints inside = over.and(CodePoints.between(block, block + (LOW_TO - LOW_FROM)));
        List<CodePoints.Range> out = new ArrayList<>();
        for (CodePoints.Range each : inside.ranges()) {
            out.add(new CodePoints.Range(LOW_FROM + each.from() - block,
                    LOW_FROM + each.to() - block));
        }
        return new CodePoints(out);
    }

    /** The first unit of the pair {@code symbol} is written as. */
    private static int highOf(int symbol) {
        return HIGH_FROM + ((symbol - PAIRED_FROM) >> 10);
    }

    private RuntimeOrder() {}
}
