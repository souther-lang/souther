package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Comparator;
import java.util.Deque;
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
 * code points the conversion answers as they stand, which every code point of its answer is where
 * converting what was converted changes nothing more. A conversion made of two does not have that,
 * and says what it leaves be by its outer one ({@link #leavingBe}).
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
     * <p>What it leaves be is what {@code conversion} answers of each code point as it stands,
     * which is every code point of its answers only where it is done again to an answer with
     * nothing more changed: said by whoever made it of two ({@link #leavingBe}).
     *
     * @param conversion what the run time answers of a text; it answers a text for a text
     */
    public static CodeMap of(UnaryOperator<String> conversion) {
        CodePoints stable = StableStarters.all();
        List<CodePoints.Range> alone = new ArrayList<>();
        int aloneFrom = -1;
        // The code points that are sent alone to one stable starter, and where.
        int[] candidates = new int[CodePoints.LAST + 1];
        int[] targets = new int[CodePoints.LAST + 1];
        int found = 0;
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
            int target = sentAloneTo(stable, codePoint, answer);
            if (target >= 0) {
                candidates[found] = codePoint;
                targets[found] = target;
                found++;
            }
        }
        if (aloneFrom >= 0) {
            alone.add(new CodePoints.Range(aloneFrom, CodePoints.LAST));
        }
        BitSet dependsOnWhatStandsBeside = dependingOnWhatStandsBeside(conversion, candidates,
                targets, found);
        List<Run> runs = new ArrayList<>();
        for (int at = 0; at < found; at++) {
            if (dependsOnWhatStandsBeside.get(at)) {
                continue;
            }
            int codePoint = candidates[at];
            Run last = runs.isEmpty() ? null : runs.getLast();
            int shift = targets[at] - codePoint;
            if (last != null && last.to() + 1 == codePoint && last.shift() == shift) {
                runs.set(runs.size() - 1, new Run(last.from(), codePoint, shift));
            } else {
                runs.add(new Run(codePoint, codePoint, shift));
            }
        }
        return new CodeMap(runs, new CodePoints(alone));
    }

    /**
     * The same map, with the code points it leaves be said by {@code alone}: for a conversion made
     * of two, the code points of what the outer one answers, which are its own.
     */
    public CodeMap leavingBe(CodePoints alone) {
        return new CodeMap(runs, alone);
    }

    /**
     * The code point {@code codePoint} is sent to when it is alone, or -1 where it is not a stable
     * starter sent to one: where the answer is more than one code point, or is not a stable
     * starter.
     */
    private static int sentAloneTo(CodePoints stable, int codePoint, String answer) {
        if (!stable.has(codePoint) || answer == null
                || answer.codePointCount(0, answer.length()) != 1) {
            return -1;
        }
        int target = answer.codePointAt(0);
        return stable.has(target) ? target : -1;
    }

    /** How many code points are asked of the conversion together. */
    private static final int ASKED_TOGETHER = 1024;

    /**
     * Which of the first {@code count} of {@code candidates} are sent somewhere else beside a
     * letter than they are alone — those at the places of the result.
     *
     * <p>The conversion of a text can turn on what stands beside a code point, and what it turns
     * on is whether a cased letter stands before it and whether one stands after: the capital sigma
     * that closes a word is lowercased as one that does not. So each is asked with a letter before
     * and none after, one after and none before, and one on both sides; and none of them is let off
     * for being sent to itself, since a conversion made of two can send a code point to itself
     * alone and not beside a letter. They are asked in turn, a thousand at a time, each with a
     * space where it has no letter, which is neither cased nor ignored in a word. A group whose
     * answer is not the answers of its members is asked again in halves.
     */
    private static BitSet dependingOnWhatStandsBeside(UnaryOperator<String> conversion,
                                                      int[] candidates, int[] targets,
                                                      int count) {
        String letter = conversion.apply("a");
        String gap = conversion.apply(" ");
        BitSet depends = new BitSet(count);
        Deque<int[]> asked = new ArrayDeque<>();
        for (int from = count; from > 0; from -= ASKED_TOGETHER) {
            asked.push(new int[] {Math.max(0, from - ASKED_TOGETHER), from});
        }
        while (!asked.isEmpty()) {
            int[] group = asked.pop();
            StringBuilder text = new StringBuilder();
            StringBuilder expected = new StringBuilder();
            for (int at = group[0]; at < group[1]; at++) {
                String own = Character.toString(candidates[at]);
                String sent = Character.toString(targets[at]);
                text.append("a").append(own).append(" ")
                        .append(" ").append(own).append("a")
                        .append("a").append(own).append("a");
                expected.append(letter).append(sent).append(gap)
                        .append(gap).append(sent).append(letter)
                        .append(letter).append(sent).append(letter);
            }
            if (conversion.apply(text.toString()).equals(expected.toString())) {
                continue;
            }
            if (group[1] - group[0] == 1) {
                depends.set(group[0]);
                continue;
            }
            int middle = (group[0] + group[1]) >>> 1;
            asked.push(new int[] {middle, group[1]});
            asked.push(new int[] {group[0], middle});
        }
        return depends;
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
