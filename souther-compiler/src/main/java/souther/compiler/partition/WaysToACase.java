package souther.compiler.partition;

import souther.compiler.collect.LatelyAsked;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.UnaryOperator;

/**
 * The way to each case a comparison's statement of several is asked in, and whether rows cross a
 * line in it, each worked out once however many lines of the statement ask.
 *
 * <p>Made for one comparison, because both answers are about the rows that reach it: the way to a
 * case is the way to the comparison with the case taken in beside it, and whether rows cross a line
 * in a case is asked of the arrivals and the reading of that comparison. The lines of a statement
 * of several are read over the same cases, and lines that part the same quantity at the same place
 * ask the same case for the same answer. What differs between lines is the cases each one holds,
 * and a case two of them hold is one question.
 *
 * <p>Whether rows cross is keyed by the line's {@link Cutting} and not by the line: two lines of
 * the statement reached along different arms of the choices before the comparison are two lines
 * and one cutting.
 *
 * <p><b>And by what the case asks of the regions, not by the case.</b> Whether rows cross a line
 * is read off the regions that hold every row along the way ({@link Reachability.Reaching#holdingEveryRow})
 * and what the case leaves the line's own quantity ({@link Cutting#leftBy}). A truth the case asks
 * of a position nothing else on the way to it turns on is in no region: a {@code Bool} is no
 * number, and asked once it contradicts nothing, closes no alternative of anything else on the way
 * and narrows nothing ({@link RowDemand.ATruth}). So two cases that differ only in such truths ask
 * the regions the same, and are one question: the cases a statement of several is taken apart into
 * by the assignments of truths beside a comparison are as many questions as the numbers they leave,
 * and not as many as the assignments. The way to each case is still its own, with every truth on
 * it: a row composed along it is a row in that case.
 *
 * <p>A way is kept while it is among the {@link #CASES_KEPT} asked last, and not for as long as the
 * comparison is read. Each is a reading of the whole region with the case taken in, and a statement
 * of several is asked in thousands of cases; the lines asking one case are read one after another,
 * so a way is asked again soon after it was worked out or not at all. One asked again after it was
 * let go is worked out again, and is the way it was.
 */
final class WaysToACase {

    /**
     * How many cases' ways are kept, and what each case puts on the way: more than the cases the
     * lines asking one case put in between in the models measured, so none of those is worked out
     * twice there.
     */
    static final int CASES_KEPT = 512;

    private final List<OnTheWay> way;
    private final Function<Proposition, List<OnTheWay>> put;
    private final Function<List<OnTheWay>, Reachability> reading;
    private final LatelyAsked<Proposition, Reachability> ways = new LatelyAsked<>(CASES_KEPT);
    private final Map<Cutting, Map<AskedOfTheRegions, Boolean>> crossings = new HashMap<>();

    /** Whether the way to the comparison is shown to ask nothing of each position asked. */
    private final Map<TermPath, Boolean> askedNothingOnTheWay = new HashMap<>();

    /**
     * What a case asks of the regions a line is crossed in: what it puts on the way less the
     * truths nothing else on the way turns on, and what it leaves the line's quantity.
     *
     * @param onTheWay      what the case puts on the way, but for those truths
     * @param onTheQuantity what the case leaves the line's own quantity, null where it leaves it
     *                      whatever it had ({@link Cutting#leftBy})
     */
    private record AskedOfTheRegions(List<OnTheWay> onTheWay, LevelRegion onTheQuantity) {}

    /**
     * @param way     what the model states on the way to the comparison
     * @param put     what a case puts on the way at the comparison
     *                ({@link ComparisonReadings.Reading#aCasePutOnTheWay})
     * @param reading the way to the comparison with what a case put on it after the way, read
     *                over what the declarations leave and taken past what a run to it got past
     */
    WaysToACase(List<OnTheWay> way, Function<Proposition, List<OnTheWay>> put,
                Function<List<OnTheWay>, Reachability> reading) {
        this.way = List.copyOf(way);
        this.put = put;
        this.reading = reading;
    }

    /** The way to the comparison with {@code decides} taken in beside it. */
    Reachability apply(Proposition decides) {
        return ways.answer(decides, asked -> reading.apply(put.apply(asked)));
    }

    /**
     * Whether rows cross the line {@code cutting} draws in the case {@code decides}, as
     * {@code asked} says of the way to it and what the case keeps the line's values to the first
     * time a case asking the regions the same is put.
     *
     * @param read the reading of the input the comparison was read against
     */
    boolean crossed(Cutting cutting, Proposition decides, InputReading read,
                    BiPredicate<Reachability, UnaryOperator<Border.Values>> asked) {
        List<OnTheWay> putOn = put.apply(decides);
        List<OnTheWay> ofTheRegions = askedOfTheRegions(putOn);
        LevelRegion onIt = cutting.leftBy(decides, read);
        Map<AskedOfTheRegions, Boolean> inCases =
                crossings.computeIfAbsent(cutting, _ -> new HashMap<>());
        AskedOfTheRegions key = new AskedOfTheRegions(ofTheRegions, onIt);
        Boolean had = inCases.get(key);
        if (had == null) {
            // Where the case asks the regions all it puts on the way, the way is its own, and kept
            // for it.
            Reachability toIt = ofTheRegions.size() == putOn.size() ? apply(decides)
                    : reading.apply(ofTheRegions);
            had = asked.test(toIt, cutting.keptTo(onIt));
            inCases.put(key, had);
        }
        return had;
    }

    /**
     * {@code putOn} less each truth it asks of a position that everything else on the way to the
     * comparison, and everything else it puts on, is shown to ask nothing of.
     */
    private List<OnTheWay> askedOfTheRegions(List<OnTheWay> putOn) {
        List<OnTheWay> out = new ArrayList<>(putOn.size());
        for (int at = 0; at < putOn.size(); at++) {
            OnTheWay entry = putOn.get(at);
            if (!(entry instanceof OnTheWay.TakenIn(var _, RowDemand.ATruth(TermPath of, var _))
                    && aloneIn(of, putOn, at))) {
                out.add(entry);
            }
        }
        return out.size() == putOn.size() ? putOn : List.copyOf(out);
    }

    /**
     * Whether everything on the way and in {@code putOn} but the entry at {@code alone} is shown to
     * ask nothing of the value at {@code of} — and that value is no element's, which is there only
     * where its container holds one.
     */
    private boolean aloneIn(TermPath of, List<OnTheWay> putOn, int alone) {
        if (of.insideAContainer()) {
            return false;
        }
        for (int at = 0; at < putOn.size(); at++) {
            if (at != alone && !WayToTheBorder.asksNothingOf(of, putOn.get(at))) {
                return false;
            }
        }
        return askedNothingOnTheWay.computeIfAbsent(of, position -> way.stream()
                .allMatch(entry -> WayToTheBorder.asksNothingOf(position, entry)));
    }
}
