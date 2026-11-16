package souther.compiler.regex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.IntStream;

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
 * <p>A composite that ends in a mark, such as {@code é}, hides it: a mark of a lesser class after
 * it is put before the mark and may compose with the letter, which the machine does not follow. It
 * is left out of what is followed, so a string that holds one is shown a value only where it is
 * held as written, and is otherwise one that may be: {@code é} followed by a combining grave is a
 * value the machine does not say is one.
 *
 * <p>Made only of the code points the language reads, and only where they are few: the machine has
 * a state for each starter among them and each class of mark. A language reading more is not made
 * here, since the machine of every string in the form is some thousands of states and a language
 * read with it by the states of the two together; its values are shown by what is held as
 * written, and every string of it may be one.
 *
 * <p>So what is said is two languages and not one ({@link Values}): the strings shown to be
 * values, which a question shown true of a value is asked of, and the strings outside which none
 * is, which one shown false is.
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

    /** Whether {@code codePoint} is a composite that ends in the mark it was made with. */
    private static boolean hidesAMark(int codePoint) {
        String parts = Normalization.normalize(Normalization.Form.NFD,
                Character.toString(codePoint));
        return parts.codePointCount(0, parts.length()) > 1
                && Normalization.combiningClass(parts.codePointBefore(parts.length())) != 0;
    }

    /**
     * The values of a language, as far as each is shown: every string of {@code surely} is a value,
     * and no value is outside {@code perhaps}. A question shown true of a string is shown of the
     * strings of {@code surely}, and one shown false of a string is shown of what is outside
     * {@code perhaps} and nowhere else.
     *
     * @param surely  strings of the language each of which is a value
     * @param perhaps strings of the language outside which none is a value, which hold
     *                {@code surely}
     */
    public record Values(Language surely, Language perhaps) {

        public Values {
            if (surely == null || perhaps == null) {
                throw new IllegalArgumentException("the values of a language are some strings");
            }
        }
    }

    /**
     * The values of {@code language} ({@link Values}), or null past what {@code meter} allows.
     *
     * <p>Where the code points it reads are few, every string in the form is followed but those
     * holding a composite that ends in a mark, which are held as written where they are and are
     * otherwise among the values that may be. Where they are many, the strings held as written are
     * the values shown, and every string of the language may be one.
     */
    public static Values of(Language language, Meter meter) {
        Language written = language.heldAsWritten().language(meter);
        if (written == null) {
            return null;
        }
        Followed followed = followedOf(language, meter);
        if (followed == null) {
            return new Values(written, language);
        }
        Language surely = followed.inTheForm().or(written, meter);
        if (surely == null) {
            return null;
        }
        if (followed.hiding().isEmpty()) {
            return new Values(surely, surely);
        }
        Language holding = CodeMap.stringsHolding(followed.hiding(), meter);
        Language hidden = holding == null ? null : language.and(holding, meter);
        Language perhaps = hidden == null ? null : surely.or(hidden, meter);
        return perhaps == null ? null : new Values(surely, perhaps);
    }

    /** The strings of a language in the form that hold no composite ending in a mark, and those
     *  composites the language reads. */
    private record Followed(Language inTheForm, CodePoints hiding) {}

    /**
     * What is followed of {@code language} ({@link Followed}), or null where the code points it
     * reads are many or the machine is more than {@code meter} allows.
     */
    private static Followed followedOf(Language language, Meter meter) {
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
        // A language of stable starters holds only values: they are in the form in any order.
        if (StableStarters.within(read).equals(read)) {
            return new Followed(language, CodePoints.NONE);
        }
        if (read.size() > MOST_READ) {
            return null;
        }
        int[] every = read.ranges().stream()
                .flatMapToInt(range -> IntStream.rangeClosed(range.from(), range.to())).toArray();
        int[] alphabet = Arrays.stream(every).filter(each -> !hidesAMark(each)).toArray();
        BitSet hiding = new BitSet();
        Arrays.stream(every).filter(StringsInNormalFormC::hidesAMark).forEach(hiding::set);
        Language followed = followed(machine, live, alphabet, meter);
        return followed == null ? null
                : new Followed(followed, CodeMap.codePointsOf(hiding));
    }

    /** The strings of {@code machine} over {@code alphabet} that are in the form. */
    private static Language followed(Automaton machine, BitSet live, int[] alphabet,
                                     Meter meter) {
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
