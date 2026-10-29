package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import java.util.function.UnaryOperator;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

/**
 * A conversion of a string read as a map on its code points, over the strings it is exactly that
 * for.
 *
 * <p>A conversion answers the full mapping of a text and then its Normalization Form C, so a code
 * point may become several, and the answer is not one code point for each code point it was handed.
 * It is exactly a map on the code points for a string whose every code point is a stable starter
 * ({@link StableStarters}) that the conversion sends to one stable starter, whatever stands beside
 * it: a string of stable starters is in NFC however they are ordered, so there is nothing for the
 * form to change, in the string or in the answer. That is the {@link #domain}, and a string of it
 * converts to the string its code points are sent to, as long as it is. A code point whose answer
 * depends on what stands beside it, such as the capital sigma that closes a word, is outside it.
 *
 * <p>What is outside the domain is not said anything of here, except by {@link #leftAlone}: the
 * code points the conversion answers as they stand, which every code point of its answer is, since
 * converting what was converted changes nothing more.
 *
 * <p>Worked out by asking the conversion itself of every code point, once, so that the map is the
 * run time's and not a table kept beside it.
 */
public final class CodeMap {

    /** The code points {@code from} to {@code to}, each sent to the one {@code shift} away. */
    private record Run(int from, int to, int shift) {

        int imageFrom() {
            return from + shift;
        }

        int imageTo() {
            return to + shift;
        }
    }

    private final List<Run> runs;
    /** The same runs by where they are sent, with how far the images of the runs up to each reach. */
    private final List<Run> byImage;
    private final int[] imageReach;
    private final CodePoints domain;
    private final CodePoints leftAlone;

    private CodeMap(List<Run> runs, CodePoints leftAlone) {
        this.runs = List.copyOf(runs);
        this.byImage = runs.stream().sorted(Comparator.comparingInt(Run::imageFrom)).toList();
        this.imageReach = new int[byImage.size()];
        int reach = -1;
        for (int i = 0; i < imageReach.length; i++) {
            reach = Math.max(reach, byImage.get(i).imageTo());
            imageReach[i] = reach;
        }
        List<CodePoints.Range> covered = new ArrayList<>();
        for (Run each : runs) {
            covered.add(new CodePoints.Range(each.from(), each.to()));
        }
        this.domain = new CodePoints(covered);
        this.leftAlone = leftAlone;
    }

    /**
     * The map {@code conversion} is on the code points it is exactly one for.
     *
     * @param conversion what the run time answers of a text; it answers a text for a text
     */
    public static CodeMap of(UnaryOperator<String> conversion) {
        CodePoints stable = StableStarters.all();
        List<Run> runs = new ArrayList<>();
        List<CodePoints.Range> alone = new ArrayList<>();
        int aloneFrom = -1;
        for (int codePoint = 0; codePoint <= CodePoints.LAST; codePoint++) {
            if (CodePoints.isSurrogate(codePoint)) {
                if (aloneFrom >= 0) {
                    alone.add(new CodePoints.Range(aloneFrom, codePoint - 1));
                    aloneFrom = -1;
                }
                continue;
            }
            String one = Character.toString(codePoint);
            String answer = conversion.apply(one);
            boolean unchanged = one.equals(answer);
            if (unchanged) {
                if (aloneFrom < 0) {
                    aloneFrom = codePoint;
                }
            } else if (aloneFrom >= 0) {
                alone.add(new CodePoints.Range(aloneFrom, codePoint - 1));
                aloneFrom = -1;
            }
            if (unchanged && !stable.has(codePoint)) {
                continue;
            }
            int target = targetOf(conversion, stable, codePoint, one, answer);
            if (target < 0) {
                continue;
            }
            Run last = runs.isEmpty() ? null : runs.getLast();
            int shift = target - codePoint;
            if (last != null && last.to() + 1 == codePoint && last.shift() == shift) {
                runs.set(runs.size() - 1, new Run(last.from(), codePoint, shift));
            } else {
                runs.add(new Run(codePoint, codePoint, shift));
            }
        }
        if (aloneFrom >= 0) {
            alone.add(new CodePoints.Range(aloneFrom, CodePoints.LAST));
        }
        return new CodeMap(runs, new CodePoints(alone));
    }

    /**
     * The code point {@code codePoint} is sent to wherever it stands, or -1 where it is not a stable
     * starter sent to one: where the answer is more than one code point, is not a stable starter, or
     * depends on what stands beside it.
     */
    private static int targetOf(UnaryOperator<String> conversion, CodePoints stable, int codePoint,
                                String one, String answer) {
        if (!stable.has(codePoint) || answer == null
                || answer.codePointCount(0, answer.length()) != 1) {
            return -1;
        }
        int target = answer.codePointAt(0);
        if (!stable.has(target)) {
            return -1;
        }
        // A letter on either side, or on both, is what a code point that closes a word is told
        // apart by: it is sent where it was alone only if it is sent there beside them too.
        String letter = "a";
        String converted = conversion.apply(letter);
        for (int beside = 1; beside < 4 && target != codePoint; beside++) {
            boolean before = (beside & 1) != 0;
            boolean after = (beside & 2) != 0;
            String together = conversion.apply(
                    (before ? letter : "") + one + (after ? letter : ""));
            if (!together.equals((before ? converted : "") + answer + (after ? converted : ""))) {
                return -1;
            }
        }
        return target;
    }

    /** The code points the map is defined on. A string of only these converts to the string its
     *  code points are sent to. */
    public CodePoints domain() {
        return domain;
    }

    /**
     * The code points the conversion answers as they stand, whether or not the map is defined
     * there. Every code point of what the conversion answers is one of these.
     */
    public CodePoints leftAlone() {
        return leftAlone;
    }

    /** The code points {@code over} holds that the map is defined on, sent where they go. */
    public CodePoints image(CodePoints over) {
        List<CodePoints.Range> out = new ArrayList<>();
        for (CodePoints.Range range : over.ranges()) {
            // The runs are in order and apart, so those ending before the range are skipped by
            // search and those starting after it end the walk.
            int low = 0;
            int high = runs.size();
            while (low < high) {
                int middle = (low + high) >>> 1;
                if (runs.get(middle).to() < range.from()) {
                    low = middle + 1;
                } else {
                    high = middle;
                }
            }
            for (int i = low; i < runs.size() && runs.get(i).from() <= range.to(); i++) {
                Run run = runs.get(i);
                int from = Math.max(range.from(), run.from());
                int to = Math.min(range.to(), run.to());
                out.add(new CodePoints.Range(from + run.shift(), to + run.shift()));
            }
        }
        return new CodePoints(out);
    }

    /** The code points of the domain that are sent to one of {@code over}. */
    public CodePoints preimage(CodePoints over) {
        List<CodePoints.Range> out = new ArrayList<>();
        for (CodePoints.Range range : over.ranges()) {
            // By where they are sent, the images of the runs up to one reach no further than
            // imageReach says, so those reaching short of the range are skipped by search.
            int low = 0;
            int high = imageReach.length;
            while (low < high) {
                int middle = (low + high) >>> 1;
                if (imageReach[middle] < range.from()) {
                    low = middle + 1;
                } else {
                    high = middle;
                }
            }
            for (int i = low; i < byImage.size() && byImage.get(i).imageFrom() <= range.to(); i++) {
                Run run = byImage.get(i);
                int from = Math.max(range.from(), run.imageFrom());
                int to = Math.min(range.to(), run.imageTo());
                if (from <= to) {
                    out.add(new CodePoints.Range(from - run.shift(), to - run.shift()));
                }
            }
        }
        return new CodePoints(out);
    }

    /** Every string of the domain, or null past what {@code meter} allows. */
    public Language strings(Meter meter) {
        return stringsOf(domain, meter);
    }

    /** Every string whose code points are among {@code symbols}, or null past what {@code meter}
     *  allows. */
    public static Language stringsOf(CodePoints symbols, Meter meter) {
        BitSet accepting = new BitSet();
        accepting.set(0);
        List<Automaton.Step> loop = symbols.isEmpty() ? List.of()
                : List.of(new Automaton.Step(symbols, 0));
        return Language.canonical(Automaton.madeOf(List.of(loop), accepting), meter);
    }

    /**
     * The strings of the domain the conversion answers a string of {@code answers} for, or null
     * past what {@code meter} allows.
     */
    public Language stringsConvertedInto(Language answers, Meter meter) {
        Automaton machine = answers.machine();
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int state = 0; state < machine.size(); state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints from = preimage(each.over());
                if (!from.isEmpty()) {
                    out.add(new Automaton.Step(from, each.to()));
                }
            }
            steps.add(out);
            accepting.set(state, machine.stopsAt(state));
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /**
     * What the conversion answers of the strings of {@code strings} that are in the domain, or null
     * past what {@code meter} allows.
     */
    public Language answersTo(Language strings, Meter meter) {
        Automaton machine = strings.machine();
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int state = 0; state < machine.size(); state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints to = image(each.over());
                if (!to.isEmpty()) {
                    out.add(new Automaton.Step(to, each.to()));
                }
            }
            steps.add(out);
            accepting.set(state, machine.stopsAt(state));
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }
}
