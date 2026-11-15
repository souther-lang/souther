package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

/**
 * The values of a language: its strings that are in Normalization Form C, which is what a
 * {@code String} holds.
 *
 * <p>{@link StringsHeldAsWritten} are the strings made of stable starters, which are in the form
 * whatever order they stand in, and are a part of the values. The rest of them hold a code point
 * that is no stable starter — a combining mark, or a starter that composes with what stands before
 * it — and a lone combining mark, or a mark after a letter it composes with nothing, is a value.
 * Whether a string is in the form is read off a machine that follows what the form looks at: the
 * last starter, and the greatest combining class of the marks since it, since a code point
 * composes with the starter before it only if no mark between them has as great a class. A string
 * is in the form if nothing in it is changed by the form, which is asked of the run time's own
 * normalization of the last starter and a mark of that class standing before the next code point.
 *
 * <p>Made only of the code points the language reads, and only where they are few: the machine has
 * a state for each starter among them and each class of mark. A language reading more is not made
 * here, and its values are said by what is held as written.
 */
public final class StringsInNormalFormC {

    private StringsInNormalFormC() {}

    /** The most code points a language may read for its values to be made here. */
    private static final int MOST_READ = 512;

    /** The most states of the language and of the form together. */
    private static final int MOST_STATES = 50_000;

    /** What the form looks at of what stands before a code point. */
    private record Before(int meeting, int greatestClass) {}

    /**
     * How {@code starter} meets each code point of {@code alphabet} standing right after it: the
     * one number that stands for the code points of the alphabet the normalization changes the two
     * of, in {@code known}.
     */
    private static int meetingsOf(int starter, int[] alphabet, Map<List<Integer>, Integer> known) {
        List<Integer> changes = new ArrayList<>();
        String first = Character.toString(starter);
        for (int each : alphabet) {
            String both = first + Character.toString(each);
            if (!Normalization.nfc(both).equals(both)) {
                changes.add(each);
            }
        }
        return known.computeIfAbsent(changes, key -> known.size());
    }

    /**
     * The strings of {@code language} that are values, or null where the code points it reads are
     * many or the machine is more than {@code meter} allows.
     */
    public static Language within(Language language, Meter meter) {
        Automaton machine = language.machine();
        BitSet live = LiveStates.of(machine);
        CodePoints read = CodePoints.NONE;
        for (int state = 0; state < machine.size(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (live.get(each.to())) {
                    read = read.or(each.over());
                }
            }
        }
        if (StableStarters.within(read).equals(read)) {
            return language;
        }
        if (read.size() > MOST_READ) {
            return null;
        }
        int[] alphabet = new int[(int) read.size()];
        int count = 0;
        for (CodePoints.Range range : read.ranges()) {
            for (int each = range.from(); each <= range.to(); each++) {
                alphabet[count++] = each;
            }
        }
        // The states of the form: what stands before, as a string the run time's normalization is
        // asked of, and the code points that may follow it.
        // What stands before decides what may follow by the last starter and the greatest class of
        // the marks since it, so a state is those two. The string it stands for is the one that
        // first came to it: a mark blocks a later one from composing with the starter by its class
        // alone, and the string is what the normalization is asked of.
        // Two starters that no code point of the alphabet composes with, or is put out of order
        // by, in the same way are one: what stands before is told by how its starter meets each
        // code point, so the starters are told apart by that and not by which they are.
        Map<List<Integer>, Integer> meets = new HashMap<>();
        Map<Integer, Integer> meetingOf = new HashMap<>();
        List<String> standing = new ArrayList<>();
        Map<Before, Integer> formAt = new HashMap<>();
        Before start = new Before(-1, 0);
        standing.add("");
        formAt.put(start, 0);
        List<Before> forms = new ArrayList<>(List.of(start));
        List<Map<Integer, Integer>> formSteps = new ArrayList<>();
        for (int at = 0; at < forms.size(); at++) {
            Before before = forms.get(at);
            Map<Integer, Integer> steps = new TreeMap<>();
            for (int next : alphabet) {
                String continued = standing.get(at) + Character.toString(next);
                if (!Normalization.nfc(continued).equals(continued)) {
                    continue;
                }
                int combining = Normalization.combiningClass(next);
                Before after = combining == 0
                        ? new Before(meetingOf.computeIfAbsent(next,
                                starter -> meetingsOf(starter, alphabet, meets)), 0)
                        : new Before(before.meeting(),
                                Math.max(before.greatestClass(), combining));
                Integer known = formAt.get(after);
                if (known == null) {
                    known = forms.size();
                    forms.add(after);
                    standing.add(combining == 0 ? Character.toString(next) : continued);
                    formAt.put(after, known);
                    if (forms.size() > MOST_STATES) {
                        return null;
                    }
                }
                steps.put(next, known);
            }
            formSteps.add(steps);
        }
        // The language and the form read together, a pair of states for each state either is in.
        Map<Long, Integer> pairAt = new HashMap<>();
        List<long[]> pairs = new ArrayList<>();
        pairAt.put(pair(Automaton.START, 0), 0);
        pairs.add(new long[] {Automaton.START, 0});
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int at = 0; at < pairs.size(); at++) {
            int state = (int) pairs.get(at)[0];
            int form = (int) pairs.get(at)[1];
            Map<Integer, BitSet> byTarget = new TreeMap<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (!live.get(each.to())) {
                    continue;
                }
                for (Map.Entry<Integer, Integer> formStep : formSteps.get(form).entrySet()) {
                    if (!each.over().has(formStep.getKey())) {
                        continue;
                    }
                    long target = pair(each.to(), formStep.getValue());
                    Integer known = pairAt.get(target);
                    if (known == null) {
                        known = pairs.size();
                        pairAt.put(target, known);
                        pairs.add(new long[] {each.to(), formStep.getValue()});
                        if (pairs.size() > MOST_STATES) {
                            return null;
                        }
                    }
                    byTarget.computeIfAbsent(known, key -> new BitSet()).set(formStep.getKey());
                }
            }
            List<Automaton.Step> out = new ArrayList<>();
            byTarget.forEach((target, points) -> out.add(
                    new Automaton.Step(CodeMap.codePointsOf(points), target)));
            steps.add(out);
            accepting.set(at, machine.stopsAt(state));
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    private static long pair(int state, int form) {
        return ((long) state << 32) | form;
    }
}
