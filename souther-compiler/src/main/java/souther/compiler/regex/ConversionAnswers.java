package souther.compiler.regex;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
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
 * not of the conversion alone. The code points answered exactly are those answered with stable
 * starters whatever stands beside them: those {@link CodeMap} sends to one, and those answered
 * with several. A string of only these is converted into their answers one after another, which is
 * in the form as it stands, since no mark stands among them for a starter to compose with.
 *
 * <p>Any other code point is answered with something the form is put over afterwards, and the
 * form composes across what stood apart: {@code ı} is answered {@code I} in uppercase, and an
 * {@code I} before a combining dot above is composed with it into {@code İ}. So nothing is said
 * of a string holding one by what its answer holds as it stands. What is said is what no
 * composition takes away: every code point the decomposition of an answer holds is in the
 * decomposition of the string the form makes of it, inside whatever it was composed into. A
 * string whose answer, however it is answered beside what stands next to it, decomposes into a
 * code point that no code point the question reads decomposes into is the string of no answer in
 * the language. {@code İ} lowercased decomposes into an {@code i} and a combining dot above, and
 * no code point of {@code [a-z]+} decomposes into the dot.
 *
 * <p>So of every code point there are three things to say about it, and the strings are those of
 * the one they are made of:
 * <ul>
 *   <li>it is answered exactly, by stable starters the language reads: the string's conversion is
 *       the answers put end to end, and the language is read through them
 *       ({@link #stringsSeenInto});</li>
 *   <li>every answer it is given decomposes into a code point nothing the language reads does: a
 *       string with it is in the language's preimage of none;</li>
 *   <li>otherwise a string with it is shown neither way.</li>
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

        /** Whether some answer it is given, alone or beside a letter, holds only {@code some}. */
        boolean someWithin(CodePoints some) {
            return holdsOnly(alone, some) || beside.stream().anyMatch(each -> holdsOnly(each, some));
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
     * @param perhaps the strings whose conversion may be in the language, which hold {@code exactly}
     *                and every value whose conversion is in it: those and the strings with a code
     *                point not answered exactly, of code points each answered in some way that
     *                decomposes into what the language's code points do
     */
    public record Seen(Language exactly, Language perhaps) {}

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
        for (Map.Entry<Integer, int[]> each : several.entrySet()) {
            if (holdsOnly(each.getValue(), read)) {
                through.put(each.getKey(), each.getValue());
            }
        }
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        // The same code points are read at many steps of a machine, so what the map sends to them
        // is worked out once for each set.
        Map<CodePoints, CodePoints> preimages = new HashMap<>();
        for (int state = 0; state < machine.size(); state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints from = preimages.computeIfAbsent(each.over(), map::preimage);
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
        // What the code points the language reads decompose into, and every code point made of
        // those: an answer is the answer of a string of the language only where it decomposes into
        // these alone.
        CodePoints composed = composedOf(read);
        if (composed == null) {
            return null;
        }
        // The code points a string may hold and be shown neither way: those not answered exactly,
        // answered in some way that decomposes into what the language's code points do. One
        // answered as it is, which the map has not and which is answered elsewhere by nothing, is
        // its own answer.
        BitSet unsaid = new BitSet();
        for (Map.Entry<Integer, Answered> each : otherwise.entrySet()) {
            if (each.getValue().someWithin(composed) && holdsInSomeValue(each.getKey())) {
                unsaid.set(each.getKey());
            }
        }
        CodePoints asItIs = composed.and(map.domain().not());
        for (CodePoints.Range range : asItIs.ranges()) {
            for (int each = range.from(); each <= range.to(); each++) {
                if (!several.containsKey(each) && !otherwise.containsKey(each)
                        && holdsInSomeValue(each)) {
                    unsaid.set(each);
                }
            }
        }
        CodePoints unknown = CodeMap.codePointsOf(unsaid);
        if (unknown.isEmpty()) {
            return new Seen(exactly, exactly);
        }
        // Beside such a code point, one answered exactly is answered with a stable starter, which
        // a mark after it may be composed into: it stands where its answer decomposes into what
        // the language's code points do.
        BitSet severalWithin = new BitSet();
        several.forEach((codePoint, answer) -> severalWithin.set(codePoint,
                holdsOnly(answer, composed)));
        CodePoints either = map.preimage(composed).or(CodeMap.codePointsOf(severalWithin))
                .or(unknown);
        // The strings of those code points with at least one shown neither way.
        CodePoints before = either.and(unknown.not());
        List<Automaton.Step> first = new ArrayList<>(List.of(new Automaton.Step(unknown, 1)));
        if (!before.isEmpty()) {
            first.add(new Automaton.Step(before, 0));
        }
        List<List<Automaton.Step>> free = List.of(first, List.of(new Automaton.Step(either, 1)));
        BitSet stops = new BitSet();
        stops.set(1);
        Language withOne = Language.canonical(Automaton.madeOf(free, stops), meter);
        Language perhaps = withOne == null ? null : exactly.or(withOne, meter);
        return perhaps == null ? null : new Seen(exactly, perhaps);
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
        // A machine reads the same code points at many of its steps — a string bounded to some
        // hundreds of code points is as many states with the same one — so what the map and the
        // answers of several code points make of a set of them is worked out once for each.
        Map<CodePoints, CodePoints> images = new HashMap<>();
        Map<CodePoints, List<Map.Entry<Integer, int[]>>> severalIn = new HashMap<>();
        for (int state = 0; state < machine.size(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints to = images.computeIfAbsent(each.over(), map::image);
                if (!to.isEmpty()) {
                    steps.get(state).add(new Automaton.Step(to, each.to()));
                }
                for (Map.Entry<Integer, int[]> point : severalIn.computeIfAbsent(each.over(),
                        over -> several.entrySet().stream()
                                .filter(one -> over.has(one.getKey())).toList())) {
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

    /** The most code points a language may read for what they decompose into to be followed. */
    private static final int MOST_READ = 512;

    /**
     * The code points whose canonical decomposition holds only what the code points of
     * {@code read} decompose into, those included: what the form may make an answer of a string
     * of {@code read} out of. Or null where {@code read} holds more than are followed.
     *
     * <p>A composition is of a code point and a mark or a jamo after it, one at a time, so each
     * code point made of those parts is reached from one of them by composing the parts in turn.
     */
    private static CodePoints composedOf(CodePoints read) {
        if (read.size() > MOST_READ) {
            return null;
        }
        BitSet made = new BitSet();
        for (CodePoints.Range range : read.ranges()) {
            for (int each = range.from(); each <= range.to(); each++) {
                made.set(each);
                Normalization.normalize(Normalization.Form.NFD, Character.toString(each))
                        .codePoints().forEach(made::set);
            }
        }
        // What composes with a code point before it is no stable starter.
        int[] after = made.stream().filter(each -> !StableStarters.all().has(each)).toArray();
        boolean grew = after.length > 0;
        while (grew) {
            grew = false;
            for (int first : made.stream().toArray()) {
                for (int second : after) {
                    String both = Normalization.nfc(Character.toString(first)
                            + Character.toString(second));
                    if (both.codePointCount(0, both.length()) == 1
                            && !made.get(both.codePointAt(0))) {
                        made.set(both.codePointAt(0));
                        grew = true;
                    }
                }
            }
        }
        return CodeMap.codePointsOf(made);
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

    /** The most code points of a set {@link #cutsAtOneOf} asks. */
    private static final int TRIED_AT_MOST = 64;

    /** What {@link #cutsAt} answered of each code point it was asked of. */
    private final Map<Integer, Boolean> cuts = new ConcurrentHashMap<>();

    /**
     * Whether the conversion cuts at some code point of {@code some} ({@link #cutsAt}), asked of
     * the code points of it up to the first few: false says only that none of those it asked is
     * one.
     */
    public boolean cutsAtOneOf(CodePoints some) {
        int tried = 0;
        for (CodePoints.Range range : some.ranges()) {
            for (int each = range.from(); each <= range.to(); each++) {
                if (tried++ == TRIED_AT_MOST) {
                    return false;
                }
                if (cuts.computeIfAbsent(each, this::cutsAt)) {
                    return true;
                }
            }
        }
        return false;
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
