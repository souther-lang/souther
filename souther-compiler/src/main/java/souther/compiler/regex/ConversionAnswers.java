package souther.compiler.regex;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;
import java.util.function.UnaryOperator;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

/**
 * What a case conversion answers of each code point, read against what a question is about: the
 * strings whose conversion is in a language that reads only stable starters
 * ({@link StableStarters}).
 *
 * <p>Whether a conversion is exact is a fact of the conversion and of the question together, and
 * not of the conversion alone. {@link CodeMap} is exact for the code points sent to one stable
 * starter, which is what a question about any string needs. A question about strings that read
 * only stable starters needs less: a code point whose answer holds a code point the question does
 * not read is the code point of no string in the language, whatever the answer is — a stable
 * starter composes with nothing beside it, so nothing the answer holds can be turned into one by
 * what stands next to it, and a code point that is no stable starter can only be composed into
 * something that is no stable starter either. {@code İ} answers an {@code i} and a combining dot
 * above, which no string of {@code [a-z]+} holds, wherever {@code İ} stands.
 *
 * <p>So of every code point there are three things to say about it for such a language, and the
 * strings are those of the one they are made of:
 * <ul>
 *   <li>it is answered exactly, by stable starters the language reads: the string's conversion is
 *       the answers put end to end, and the language is read through them
 *       ({@link #stringsSeenInto});</li>
 *   <li>it is answered, whatever stands beside it, with something the language does not hold: a
 *       string with it is in the language's preimage of none;</li>
 *   <li>it is answered in a way that is not said here — it turns on what stands beside it, or it is
 *       no stable starter and may be composed into one — and a string with it is shown neither
 *       way.</li>
 * </ul>
 *
 * <p>A conversion also commutes with where a string is cut at a code point that nothing it does
 * reaches across ({@link #cutsAt}): {@code lowercase(x@y)} is {@code lowercase(x)@lowercase(y)}.
 */
public final class ConversionAnswers {

    /** What a code point outside {@link CodeMap#domain} is answered, alone and beside a letter. */
    private record Answered(int[] alone, boolean beyondWhatStandsBeside, List<int[]> beside) {

        /** Whether the answers do not turn on what stands beside, and are stable starters. */
        boolean exact() {
            return !beyondWhatStandsBeside && holdsOnly(alone, StableStarters.all());
        }

        boolean mentions(int symbol) {
            return holds(alone, symbol) || beside.stream().anyMatch(each -> holds(each, symbol));
        }
    }

    private static boolean holdsOnly(int[] codePoints, CodePoints symbols) {
        for (int each : codePoints) {
            if (!symbols.has(each)) {
                return false;
            }
        }
        return true;
    }

    private static boolean holds(int[] codePoints, int symbol) {
        for (int each : codePoints) {
            if (each == symbol) {
                return true;
            }
        }
        return false;
    }

    /**
     * The strings whose conversion is in a language, as far as that is said.
     *
     * @param exactly the strings whose conversion is in the language, each of them: a string of
     *                code points answered exactly, put through the language
     * @param perhaps the strings whose conversion may be in the language, which hold {@code exactly}:
     *                those and the strings with a code point answered in a way not said here, and
     *                no code point answered with what the language does not hold
     * @param asLong  whether a string of {@code exactly} is converted into one as long as it is:
     *                no code point it may hold is answered with several
     */
    public record Seen(Language exactly, Language perhaps, boolean asLong) {}

    private final CodeMap map;
    private final UnaryOperator<String> conversion;
    /** The code points answered exactly with several stable starters, which the map has not. */
    private final NavigableMap<Integer, int[]> several = new TreeMap<>();
    /** The code points answered in a way the map does not say, and that are not in {@code several}. */
    private final NavigableMap<Integer, Answered> otherwise = new TreeMap<>();

    private ConversionAnswers(CodeMap map, UnaryOperator<String> conversion) {
        this.map = map;
        this.conversion = conversion;
        String letter = conversion.apply("a");
        for (Map.Entry<Integer, String> each : map.answeredElsewhere().entrySet()) {
            int codePoint = each.getKey();
            int[] alone = each.getValue().codePoints().toArray();
            List<int[]> beside = new ArrayList<>();
            boolean dependsOnWhatStandsBeside = false;
            String own = Character.toString(codePoint);
            for (String[] around : new String[][] {{"a", ""}, {"", "a"}, {"a", "a"}}) {
                String answer = conversion.apply(around[0] + own + around[1]);
                String before = around[0].isEmpty() ? "" : letter;
                String after = around[1].isEmpty() ? "" : letter;
                if (answer == null || !answer.startsWith(before) || !answer.endsWith(after)
                        || answer.length() < before.length() + after.length()) {
                    // Not made of the letter's answer and this one's: nothing here is said of it.
                    dependsOnWhatStandsBeside = true;
                    beside.add(answer == null ? alone : answer.codePoints().toArray());
                    continue;
                }
                int[] between = answer.substring(before.length(), answer.length() - after.length())
                        .codePoints().toArray();
                beside.add(between);
                dependsOnWhatStandsBeside |= !Arrays.equals(between, alone);
            }
            Answered answered = new Answered(alone, dependsOnWhatStandsBeside, beside);
            if (StableStarters.all().has(codePoint) && answered.exact()) {
                several.put(codePoint, alone);
            } else {
                otherwise.put(codePoint, answered);
            }
        }
    }

    /**
     * The code points the conversion may answer with more than one: those it answers so alone or
     * beside a letter. A string of none of them is converted into one no longer than it is, since
     * the form the answer is put in only joins code points.
     */
    public CodePoints mayLengthen() {
        BitSet out = new BitSet();
        several.keySet().forEach(out::set);
        otherwise.forEach((codePoint, answered) -> {
            if (answered.alone().length > 1
                    || answered.beside().stream().anyMatch(each -> each.length > 1)) {
                out.set(codePoint);
            }
        });
        return CodeMap.codePointsOf(out);
    }

    /** What {@code conversion} answers of each code point, read off {@code map} made of it. */
    public static ConversionAnswers of(CodeMap map, UnaryOperator<String> conversion) {
        return new ConversionAnswers(map, conversion);
    }

    /**
     * The strings whose conversion is in {@code answers}, or null where that is not said: where
     * the language reads a code point that is no stable starter, or the machines are more than
     * {@code meter} allows.
     */
    public Seen stringsSeenInto(Language answers, Meter meter) {
        Automaton machine = answers.machine();
        BitSet live = LiveStates.of(machine);
        CodePoints read = CodePoints.NONE;
        for (int state = 0; state < machine.size(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (live.get(each.to())) {
                    read = read.or(each.over());
                }
            }
        }
        if (!StableStarters.within(read).equals(read)) {
            return null;
        }
        // The code points answered by several stable starters the language reads, and where.
        NavigableMap<Integer, int[]> through = new TreeMap<>();
        BitSet sent = new BitSet();
        for (Map.Entry<Integer, int[]> each : several.entrySet()) {
            if (holdsOnly(each.getValue(), read)) {
                through.put(each.getKey(), each.getValue());
                sent.set(each.getKey());
            }
        }
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int state = 0; state < machine.size(); state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints from = map.preimage(each.over());
                if (!from.isEmpty()) {
                    out.add(new Automaton.Step(from, each.to()));
                }
            }
            Map<Integer, BitSet> byEnd = new TreeMap<>();
            for (Map.Entry<Integer, int[]> each : through.entrySet()) {
                for (int end : endsOf(machine, state, each.getValue())) {
                    byEnd.computeIfAbsent(end, key -> new BitSet()).set(each.getKey());
                }
            }
            byEnd.forEach((end, points) -> out.add(
                    new Automaton.Step(CodeMap.codePointsOf(points), end)));
            steps.add(out);
            accepting.set(state, machine.stopsAt(state));
        }
        Language exactly = Language.canonical(Automaton.madeOf(steps, accepting), meter);
        if (exactly == null) {
            return null;
        }
        // The code points a string may hold and be shown neither way: answered in a way not said
        // here, and not answered with what the language does not hold in every way it may be.
        BitSet unsaid = new BitSet();
        for (Map.Entry<Integer, Answered> each : otherwise.entrySet()) {
            if (!neverHolds(each.getValue(), read) && holdsInSomeValue(each.getKey())) {
                unsaid.set(each.getKey());
            }
        }
        // A code point answered exactly with stable starters the language does not read is
        // answered with what it does not hold, and is no more said than those.
        CodePoints said = map.preimage(read).or(CodeMap.codePointsOf(sent));
        CodePoints unknown = CodeMap.codePointsOf(unsaid);
        boolean asLong = through.isEmpty();
        if (unknown.isEmpty()) {
            return new Seen(exactly, exactly, asLong);
        }
        CodePoints either = said.or(unknown);
        List<List<Automaton.Step>> free = List.of(
                List.of(new Automaton.Step(said, 0), new Automaton.Step(unknown, 1)),
                List.of(new Automaton.Step(either, 1)));
        BitSet stops = new BitSet();
        stops.set(1);
        Language withOne = Language.canonical(Automaton.madeOf(free, stops), meter);
        Language perhaps = withOne == null ? null : exactly.or(withOne, meter);
        return perhaps == null ? null : new Seen(exactly, perhaps, asLong);
    }

    /**
     * What the conversion answers of the strings of {@code strings}, every code point of which is
     * answered exactly ({@link Seen#exactly}), or null past what {@code meter} allows.
     */
    public Language answersTo(Language strings, Meter meter) {
        Automaton machine = strings.machine();
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int state = 0; state < machine.size(); state++) {
            steps.add(new ArrayList<>());
            accepting.set(state, machine.stopsAt(state));
        }
        for (int state = 0; state < machine.size(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints to = map.image(each.over());
                if (!to.isEmpty()) {
                    steps.get(state).add(new Automaton.Step(to, each.to()));
                }
                for (Map.Entry<Integer, int[]> point : several.entrySet()) {
                    if (!each.over().has(point.getKey())) {
                        continue;
                    }
                    // The answer is read through states of its own, one for each code point of it
                    // but the last, which leads where the code point does.
                    int[] answer = point.getValue();
                    int from = state;
                    for (int at = 0; at < answer.length; at++) {
                        boolean last = at == answer.length - 1;
                        int next = last ? each.to() : steps.size();
                        if (!last) {
                            steps.add(new ArrayList<>());
                        }
                        steps.get(from).add(new Automaton.Step(CodePoints.of(answer[at]), next));
                        from = next;
                    }
                }
            }
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /**
     * Whether some value holds the code point: a value is held in Normalization Form C, so one
     * that normalization turns into something else, as it does the Kelvin sign into a {@code K}, is
     * the code point of no value, and what is said of the strings that hold it is said of no one.
     */
    private static boolean holdsInSomeValue(int codePoint) {
        return Normalizer.isNormalized(Character.toString(codePoint), Normalizer.Form.NFC);
    }

    /**
     * Whether every answer a code point is given, alone and beside a letter, holds a code point
     * {@code read} does not: then a string with it is in no language that reads {@code read}, since
     * what is not a stable starter of the language stays in the answer however it is composed.
     */
    private static boolean neverHolds(Answered answered, CodePoints read) {
        return !holdsOnly(answered.alone(), read) && answered.beside().stream()
                .noneMatch(each -> holdsOnly(each, read));
    }

    /** The states {@code machine} is in after one more symbol, from {@code from}. */
    private static BitSet endsOfWalk(Automaton machine, BitSet from, int symbol) {
        BitSet out = new BitSet();
        for (int state = from.nextSetBit(0); state >= 0; state = from.nextSetBit(state + 1)) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (each.over().has(symbol)) {
                    out.set(each.to());
                }
            }
        }
        return out;
    }

    private static int[] endsOf(Automaton machine, int state, int[] symbols) {
        BitSet at = new BitSet();
        at.set(state);
        for (int symbol : symbols) {
            at = endsOfWalk(machine, at, symbol);
            if (at.isEmpty()) {
                break;
            }
        }
        return at.stream().toArray();
    }

    /**
     * Whether the conversion makes no {@code separator} that the string did not hold, and answers
     * each it held as it stands: it is a stable starter sent to itself, no other code point is sent
     * to it, and none is answered with it, alone or beside a letter. So the separators of a string
     * converted are those of the string, in the same places.
     *
     * <p>{@code ŉ} is answered {@code ʼN} in uppercase, and a separator that is a composite a
     * normalization could make of two code points answered apart is none of these either.
     */
    public boolean keepsSeparator(int separator) {
        String alone = Character.toString(separator);
        if (!StableStarters.all().has(separator)
                || !map.sentToThemselves().has(separator)
                || !map.preimage(CodePoints.of(separator)).equals(CodePoints.of(separator))
                || !Normalization.normalize(Normalization.Form.NFD, alone).equals(alone)) {
            return false;
        }
        for (int[] each : several.values()) {
            if (holds(each, separator)) {
                return false;
            }
        }
        return otherwise.values().stream().noneMatch(each -> each.mentions(separator));
    }

    /**
     * Whether the conversion of a string cut at {@code separator} is the conversion of each part
     * with the separator between them: it keeps the separators ({@link #keepsSeparator}), and
     * nothing it does reaches across one.
     *
     * <p>The conversions that turn on what stands beside a code point — a capital sigma closes a
     * word — are asked of the separator standing among letters and sigmas, since a code point that
     * is cased, or ignored between cased letters, is no cut.
     */
    public boolean cutsAt(int separator) {
        if (!keepsSeparator(separator)) {
            return false;
        }
        String cut = Character.toString(separator);
        for (String before : List.of("", "a", "Α", "ΑΣ", "Σ")) {
            for (String after : List.of("", "a", "Α", "Σ", "ΣΑ")) {
                String together = conversion.apply(before + cut + after);
                String apart = conversion.apply(before) + cut + conversion.apply(after);
                if (together == null || !together.equals(apart)) {
                    return false;
                }
            }
        }
        return true;
    }
}
