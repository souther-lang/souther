package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Target;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * What a reason reads as to a person.
 *
 * <p>An {@link Incompleteness} is data rather than a sentence, which is what lets a build count and
 * match on it. Two things print one for a reader — the report, and the note beside the rows
 * {@code --generate} writes — and both printed the enum's own name for a while. That told an author
 * with a type error in front of them that their runtime was missing, the code having been named
 * after one of the things it covers.
 *
 * <p>One wording, written once. Two renderers of the same fact drift, and the two here are read
 * side by side in the same terminal.
 *
 * <p><b>The rule this is held to.</b> A sentence here is keyed on the code and nothing else, so it
 * may say only what is true at <em>every</em> place that writes that code. The code is not what
 * happened; the producer is, and two producers writing one code mean two different things by it.
 * Where a consequence holds at one producer and not another, it belongs to the producer and cannot
 * be recovered from the code — the value would have to carry it. Nothing here may reach for it.
 *
 * <p>That rule is the whole of what this class gets wrong when it gets something wrong, and it has
 * already done so twice: once by writing a sentence for every code without reading any producer,
 * and once by giving a linkage failure the consequence its first producer has and its other two do
 * not.
 *
 * <p><b>Where the words come from.</b> The sentence is written here and the subject is not. A reason
 * names its subject as an identity, and a source id is a position in a list under a build. What to
 * call a source is the caller's to answer and depends on which files are being read beside it, so it
 * arrives as a {@link SourceNameResolver} rather than being read off the reason. That is the third
 * thing this class got wrong, and it printed a file index where a file name belongs.
 */
final class Reasons {

    /**
     * What happened, said as what happened — and no further than every producer agrees.
     *
     * <p>Each has been read against its own. {@code ROW_UNDECIDED} and
     * {@code ROW_EVALUATION_LIMIT_REACHED} have one producer between them, a switch over what
     * stopped the row, and they are two codes because the sentence below could say nothing of the
     * phases it was written over that was true at all of them: a row a figure stopped is one a run
     * that allows more keeps, and a row the evaluation had no answer for is not.
     * {@code OBSERVATION_ABSENT} has two and they mean the same thing about two different subjects,
     * which is why it is the one code whose sentence reads what it is about;
     * {@code INSTRUMENTATION_ABSENT} has one, on a branch taken only where arm coverage was asked
     * for and returning no rows, so the sentence may name the request and the empty result both.
     *
     * <p>{@code LINKAGE_FAILED} has one now and had three. The other two were a fill and a boundary
     * that could not build a candidate, and both were things the generator did rather than things a
     * measurement could not read; they say so in the generator's own vocabulary now. What is left
     * is an example whose evaluation raised one, where nothing was observed — so the sentence may
     * say the rows did not run, which it could not while three producers disagreed about it.
     *
     * <p>The rest keep the shape they had, which asserts nothing the code does not already say.
     * The two value codes have been read as well. {@code VALUE_TRUNCATED} has one producer;
     * {@code VALUE_UNREADABLE} has five — a parameter that is not there, a field chain that leads
     * nowhere, a value the observer could not read, a value in none of the classes, and a position
     * some row could not be placed at — which agree that the value could not be read and say
     * nothing about why, so that is where the sentence stops. The two are apart because what an
     * author does about them is: one goes away if the fixture is written smaller and the other
     * does not.
     *
     * <p>Every code has one now, which is what it means for this enum to be the vocabulary a report
     * is written in. What the generator has to say about its own run is said in its own words, by
     * the block that prints it: a position it left out and a search that ended are things it did,
     * not things a measurement could not read.
     */
    static String said(Incompleteness.Fact gap, SourceRendering rendering) {
        String subject = gap.shown(rendering);
        return switch (gap.code()) {
            // Its two producers are about two things, so the sentence says which it is about. One
            // is a source nothing could read the contents of, where what went unread is every row
            // it holds; the other is a row of a source that produced no observation, and that row
            // is what went unread. Written as one sentence over both subjects, it said of a row
            // what is only true of a file.
            //
            // Over what it is about and not over the scope that follows from it, and with the rest
            // refused rather than left to whichever sentence came second. The two kinds are the two
            // this compiler writes; a third would be a thing nobody has said what happened to, and
            // taking the file's sentence for it is how a reader is told something that was never
            // established. Read off the sum, so an arm added to it is answered for here.
            case OBSERVATION_ABSENT -> switch (gap.target()) {
                case Target.OfRow _ -> String.format(
                        "nothing was observed for `%s`, so what it covers is unknown", subject);
                case Target.OfSource _ -> String.format(
                        "no rows were read from `%s`, so what they cover is unknown", subject);
                case Target.OfBehavior _, Target.OfModule _, Target.AtPosition _ ->
                        throw new IllegalArgumentException("nothing observed is about a row or"
                                + " about a source nothing could read the contents of: " + gap);
            };
            case LINKAGE_FAILED -> String.format(
                    "the classes for `%s` would not link, so its rows did not run", subject);
            case ROW_UNDECIDED -> String.format(
                    "a row of `%s` did not come back, so what it covers is unknown", subject);
            case ROW_EVALUATION_LIMIT_REACHED -> String.format(
                    "a row of `%s` was stopped by a limit it was evaluated under, so what it covers"
                            + " is unknown", subject);
            case ANSWERER_NOT_ESTABLISHED -> String.format(
                    "a row of `%s` was not run against what answers it, because nothing could"
                            + " establish that it was built against this model", subject);
            case INSTRUMENTATION_ABSENT -> String.format(
                    "the classes `%s` needed for arm coverage could not be made, so none of its"
                            + " rows were read", subject);
            case IMPLEMENTATION_NOT_MADE -> String.format(
                    "a row of `%s` was not run because this compile made no implementation for it,"
                            + " so what it covers is unknown", subject);
            case VALUE_UNREADABLE -> String.format(
                    "a row's value at `%s` could not be read, so which class it is in is unknown",
                    subject);
            case VALUE_TRUNCATED -> String.format(
                    "the observation at `%s` was stopped by a limit, so which class it is in is"
                            + " unknown", subject);
            case VALUE_NOT_WORKED_OUT -> String.format(
                    "a row's value at `%s` was read, and the number it comes to has no"
                            + " representation this compiler holds, so which class it is in is"
                            + " unknown", subject);
            case VALUE_ROOM_EXCEEDED -> String.format(
                    "a row's value at `%s` was read, and this host had no room to work out the"
                            + " number it comes to, so which class it is in is unknown", subject);
        };
    }

    /** What the budgets of this compiler's that stopped something are called where a reader meets
     *  them: each in its own words ({@link CompositionBudget#counts}). */
    static String said(CanonicalSelection<CompositionBudget> budgets) {
        List<String> out = new ArrayList<>();
        for (CompositionBudget each : budgets.written()) {
            out.add(each.counts());
        }
        return String.join(", ", out);
    }

    /**
     * What a population this compiler writes some of is called where a reader meets one.
     *
     * <p>Its own sentence and not one of the figures'. Nothing here is a number, so what a reader
     * is told is what this compiler writes rather than how much of it — and a population added
     * arrives here as a compile error rather than as a name nobody wrote a sentence for.
     */
    static String writes(CanonicalSelection<CompositionRepertoire> repertoires) {
        List<String> out = new ArrayList<>();
        for (CompositionRepertoire each : repertoires.written()) {
            out.add(switch (each) {
                case WAYS_A_TOTAL_IS_SPREAD ->
                        "the ways a total may be spread over what adds up to it";
                case PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE ->
                        "the places on a line between two positions a pair is tried at";
                case VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS ->
                        "the values that answer several of their own numbers";
                case PLACES_IN_A_RUN_THAT_ARE_NAMED ->
                        "the places inside one run a value is named at";
                case ELEMENTS_CHOSEN_FOR_A_COUNT ->
                        "the elements chosen for how many of them meet a statement";
                case KEYS_PLACED_AT_THE_NUMBER_THEIR_ELEMENTS_COME_TO ->
                        "the keys a number their elements come to turns on, other than the one"
                                + " placed at it, and the containers that ask for more elements"
                                + " of a key than one";
                case KEYS_OF_ONE_FOLD_ASKED_TOGETHER ->
                        "the keys of one fold asked for together at values other than the ones"
                                + " tried, and a key only counted at a number other than the"
                                + " first total's";
                case ENDS_OF_A_KEY_WRITTEN_AS_ONE_ELEMENT ->
                        "the ends of a key's values among more than one element of the key";
                case ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR ->
                        "the elements whose computed number is made of several fields, chosen"
                                + " by a flag, chosen by their case or chosen by where they"
                                + " stand";
                case MIXES_OF_CASES_A_TOTAL_IS_SPREAD_OVER ->
                        "the containers mixing the cases a computed number is chosen by";
                case TREES_WRITTEN_FOR_A_COUNT ->
                        "the trees that hold a count of nodes deeper than one node below the root";
                case STRINGS_A_CASE_CONVERSION_IS_WRITTEN_FOR ->
                        "the strings whose case conversion holds a count of code points of a"
                                + " class by other code points than the class's own";
            });
        }
        return String.join(", ", out);
    }

    /**
     * What a number a search could not hold is called where a reader meets one: what it was working
     * out, and whether a host with more room would hold it.
     *
     * <p>Its own sentence and not a figure's or a population's. No wider run of this compiler holds
     * either kind, since no figure stopped it; what a reader can still do differs by the second half
     * — measure on a machine with more room, or nothing — so it is said with every one of them, and
     * a kind added arrives here as a compile error rather than as a name nobody wrote a sentence for.
     */
    static String unheld(CanonicalSelection<CompositionCapacity> capacities) {
        List<String> out = new ArrayList<>();
        for (CompositionCapacity each : capacities.written()) {
            String what = switch (each.where()) {
                case PLACES_A_PAIR_IS_WALKED_TO -> "the next place along a pair's line";
                case PLACES_A_DISTANCE_MOVES_A_POSITION_TO ->
                        "the place a distance moves one of a pair to";
                case VALUES_OF_A_PROGRESSION_WALKED_TO -> "the next value of a progression";
                case VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO ->
                        "the next value of a position on the way";
                case VALUES_A_TOTAL_IS_SPREAD_OVER -> "one element's share of a total";
                case THE_LEAST_COUNT_ASKED_FOR -> "the least count the conditions on a count leave";
                case COUNTS_AN_ITEM_IS_TRIED_AT -> "a count a line on a count is tried at";
                case PLACES_AN_ELEMENT_TURNS_AT ->
                        "a place a statement about an element turns over at";
            };
            out.add(what + switch (each.why()) {
                case MORE_ROOM_COULD_ANSWER -> ", which this host had no room to work out";
                case NO_REPRESENTATION_EXISTS -> ", which has no representation this compiler holds";
            });
        }
        return String.join("; ", out);
    }

    /**
     * What a search that came to nothing met of this compiler's, said before what it came to.
     *
     * <p>Before, because it is what the word after it is worth. A reader who has been told that
     * this compiler stopped reads the word as the answer of a search that did not finish; a reader
     * given the word first has already made what they were going to make of it.
     *
     * <p>Two clauses and not one list. A figure is a number somebody raises and reaching it is why
     * the search went no further; a population this writes some of is work nobody has done, and no
     * number anybody raises reaches the rest of it. Run together, an author reads the second as
     * something to raise and finds that raising it changes nothing.
     *
     * <p>Empty where nothing of this compiler's was met, which is a search that came back about the
     * model and has no opening of this kind to make.
     */
    static String met(CompositionShortfall shortfall) {
        return met(PublicationOrders.COMPOSITION_BUDGETS.keep(shortfall.figures()),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(shortfall.populations()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(shortfall.unheld()),
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of()));
    }

    /** The same, of a search that came to nothing: what it met, and what cut its plan short. */
    static String met(CameToNothing came) {
        return met(PublicationOrders.COMPOSITION_BUDGETS.keep(came.met().figures()),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(came.met().populations()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(came.met().unheld()),
                PublicationOrders.COMPOSITION_BUDGETS.keep(came.planCut()));
    }

    /**
     * The same, of what was met already put in the order each kind is said in.
     *
     * <p>A figure that cut the plan short is said as a limit on the plan and never as a stop. The
     * search ran to the end of what it was handed, or was never made, so a reader told it stopped
     * would go looking for a search that did not finish. Nor as a search over a plan cut short:
     * where nothing was planned, no search was made, and the word after the clause says so.
     */
    static String met(CanonicalSelection<CompositionBudget> figures,
                      CanonicalSelection<CompositionRepertoire> populations,
                      CanonicalSelection<CompositionCapacity> unheld,
                      CanonicalSelection<CompositionBudget> planCut) {
        List<String> out = new ArrayList<>();
        if (!figures.isEmpty()) {
            out.add("this compiler stopped at " + said(figures));
        }
        if (!planCut.isEmpty()) {
            out.add("this compiler's plan of the value was limited by " + said(planCut));
        }
        if (!populations.isEmpty()) {
            out.add("this compiler writes some of " + writes(populations)
                    + " rather than all of them");
        }
        if (!unheld.isEmpty()) {
            out.add("this compiler could not hold " + unheld(unheld));
        }
        return out.isEmpty() ? "" : String.join(", and ", out) + ": ";
    }

    private Reasons() {}
}
