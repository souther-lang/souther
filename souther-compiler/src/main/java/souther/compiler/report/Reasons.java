package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.List;

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
     * {@code OBSERVATION_ABSENT} has two and they mean the same thing; {@code INSTRUMENTATION_ABSENT}
     * has one, on a branch taken only where arm coverage was asked for and returning no rows, so
     * the sentence may name the request and the empty result both.
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
            case OBSERVATION_ABSENT -> String.format(
                    "no rows were read from `%s`, so what they cover is unknown", subject);
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
            case VALUE_UNREADABLE -> String.format(
                    "a row's value at `%s` could not be read, so which class it is in is unknown",
                    subject);
            case VALUE_TRUNCATED -> String.format(
                    "the observation at `%s` was stopped by a limit, so which class it is in is"
                            + " unknown", subject);
        };
    }

    /**
     * What a budget of this compiler's is called where a reader meets one.
     *
     * <p>Its own words and not the constant's name. What the compiler calls a figure is a name for
     * the code that reads it; what a reader wants is what this compiler declined to do, in a phrase
     * they can act on — and a budget added arrives here as a compile error rather than as a name
     * nobody wrote a sentence for.
     */
    static String said(CanonicalSelection<CompositionBudget> budgets) {
        List<String> out = new ArrayList<>();
        for (CompositionBudget each : budgets.written()) {
            out.add(switch (each) {
                case ELEMENTS_A_PROPOSAL_HOLDS -> "how many elements a proposed collection holds";
                case CHARACTERS_A_PROPOSAL_HOLDS -> "how many characters a proposed string holds";
                case PAIRINGS_BUILT_AT_ONCE -> "how many of a map's pairings are built at once";
                case ELEMENTS_A_TOTAL_IS_SPREAD_OVER ->
                        "how many elements a total is spread over";
                case SHAPES_OF_A_TOTAL_OFFERED -> "how many containers are offered for one total";
                case WAYS_DOWN_TO_A_TOTAL_TRIED ->
                        "how many ways down to what a total adds up are tried";
                case PLACES_A_PAIR_IS_TRIED_AT -> "how many places a pair is tried at";
                case PLACES_A_PAIR_IS_LOOKED_AT ->
                        "how many places along a pair's line are looked at";
                case STEPS_A_SEARCH_MAY_TAKE -> "how many steps a search takes";
                case ASSIGNMENTS_A_SEARCH_COMPOSES -> "how many assignments a search composes";
                case VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED ->
                        "how many values of an unbounded progression are tried";
                case LEVELS_A_SIDE_IS_ASKED_AT -> "how many levels a side is asked at";
                case TIMES_THE_RULES_ARE_ASKED_AGAIN -> "how often the rules are read again";
                case VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT ->
                        "how many values a position on the way is tried at";
                case PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT ->
                        "how many places of a position on the way are looked at";
                case VALUES_A_POINT_IS_TRIED_WITH -> "how many values a point is tried with";
                case DEPTH_A_CONSTRUCTION_PLAN_DESCENDS -> "how deep a value is built";
                case PATHS_OF_A_DECISION_READ ->
                        "how many paths through one body a decision is read for";
                case NUMBERS_OF_A_SET_TRIED ->
                        "how many of the numbers a class admits are tried";
            });
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
            });
        }
        return String.join(", ", out);
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
        if (shortfall.nothing()) {
            return "";
        }
        List<String> out = new ArrayList<>();
        if (!shortfall.figures().isEmpty()) {
            out.add("this compiler stopped at "
                    + said(PublicationOrders.COMPOSITION_BUDGETS.keep(shortfall.figures())));
        }
        if (!shortfall.populations().isEmpty()) {
            out.add("this compiler writes some of "
                    + writes(PublicationOrders.COMPOSITION_REPERTOIRES.keep(
                            shortfall.populations()))
                    + " rather than all of them");
        }
        return String.join(", and ", out) + ": ";
    }

    private Reasons() {}
}
