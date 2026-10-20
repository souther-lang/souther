package souther.compiler.partition;

import souther.compiler.observe.Figure;
import souther.compiler.observe.RunSensitivity;

/**
 * A figure this compiler holds a piece of its own work to.
 *
 * <p>What reaching one does is the member's to say and not this sentence's — one of them changes
 * how the work is done and gives nothing up at all. So what they have in common is only that
 * somebody wrote a bound down and that raising it is a thing a person could decide to do.
 *
 * <p>One member per place that reaches a figure, and the figure is here rather than at the place.
 * What a reader wants to know is which of these was reached, and a name written beside a number
 * somewhere else is a second declaration of the same policy — the two part the first time one of
 * them is raised.
 *
 * <p><b>A cause and not an outcome.</b> Reaching one of these says what this compiler declined to
 * do and says nothing about the model: the value it did not build may be the easiest one in the
 * file to write by hand. What the reaching did is a separate question, and it is not one question:
 *
 * <ul>
 * <li>a search goes no further, and what it had reached is carried out with the figure;
 * <li>another thing a search runs against goes no further — a plan short of the value's positions
 *     leaves a search that ran to the end of less than the point had;
 * <li>nothing is given up at all, and the work carries on by a wider way that omits none of it.
 * </ul>
 *
 * <p>So a reader may not take a member for any of the three. The first two are carried and the
 * third is not, and which a member is is written where the member is — including, for the third,
 * why there is nothing to carry. A figure named here with no carrier and no such sentence is one
 * somebody has not finished.
 *
 * <p>Nor does the first divide once and for all. A search that had produced nothing when it stopped
 * leaves the point unestablished, and one that had produced something leaves an offer that is some
 * of what there was — so the same member appears on both sides and is neither of them.
 *
 * <p><b>Every figure is written down here, and none is the size of the walk it bounds.</b> A figure
 * set to how many pieces a walk has is reached on every run and on none: it says what this compiler
 * is made of rather than what one search declined, and a reader handed it is told to raise something
 * that stopped nothing. What such a number was saying belongs to
 * {@link CompositionRepertoire}, which is a population this compiler offers some of and is not a
 * number anybody raises.
 */
public enum CompositionBudget {

    /** How many elements a proposed collection is worth building. A row is offered for somebody to
     *  read and complete, and a minimum past this asks for one nobody would. */
    ELEMENTS_A_PROPOSAL_HOLDS(64),

    /** How many characters a proposed string is worth building. Its own figure, because a string of
     *  sixty-five is one literal where a collection of sixty-five is sixty-five values each built in
     *  turn — holding the two to one number bounds a string by something about collections. */
    CHARACTERS_A_PROPOSAL_HOLDS(4096),

    /** How many pairings of what a map's key and value propose are built at once. Every pair is
     *  built before any of them is tried, so this bounds what is allocated rather than what is
     *  walked. */
    PAIRINGS_BUILT_AT_ONCE(64),

    /** How many elements a container built to reach a total is worth carrying. Its own figure and
     *  not {@link #ELEMENTS_A_PROPOSAL_HOLDS}, though they agree: held as one, a change made for one
     *  of them would move the other for no reason anybody could state. */
    ELEMENTS_A_TOTAL_IS_SPREAD_OVER(64),

    /** How many containers are offered for one total. They are alike to the total, so what a fifth
     *  buys is another row reading like the last. */
    SHAPES_OF_A_TOTAL_OFFERED(4),

    /** How many elements a container composed for how many of them meet a statement is tried
     *  with. Walked from none up, so a count is met at the least size that holds it; a size past
     *  this is one where a smaller container would already have met any count a line is drawn
     *  near. */
    ELEMENTS_A_COUNT_IS_COMPOSED_WITH(16),

    /** How many containers are offered for one count. A second meets the count with other
     *  elements beside it, which is a different row where the first one does not stand. */
    CONTAINERS_A_COUNT_IS_OFFERED(4),

    /** How many ways of sharing a size out among the values a count's elements are drawn from
     *  are looked at, over every size tried. The ways grow with the size and with how many ways
     *  an element answers the statements, and each is checked against every count before any is
     *  built. */
    SHARES_A_COUNT_IS_TRIED_AT(4096),

    /** How many combinations of how often each of several keys occurs are tried for the lists of
     *  an outer list. They multiply with the keys, and each is a container composed whole, so a
     *  walk over them is held to this and not to the containers it offers, which count only the
     *  ones that were built. */
    COUNTS_OF_KEYS_TRIED(4096),

    /** How many values of an element of a type that has only so many are read for the counts its
     *  container is composed for, each read for every statement the counts are of. Past it the
     *  values left are not offered, and the container is composed of the ones read. The same
     *  values are what the most a count of a set's elements comes to is read off; past it that
     *  count keeps the most the set holds, and the points between are searched rather than
     *  refused. */
    VALUES_AN_ELEMENT_IS_CHOSEN_AMONG(256),

    /** How many ways down to the number a total is read from are tried. Its own figure and not
     *  {@link #SHAPES_OF_A_TOTAL_OFFERED}: a way that plans is not a container that was offered, and
     *  charging one to the other leaves a case never tried because an earlier one planned and built
     *  nothing. What multiplies here is the cases of every sum the way down crosses. */
    WAYS_DOWN_TO_A_TOTAL_TRIED(8),

    /** How many ways of writing the containers a row's conditions hand values to are tried, where
     *  their names are spread by the cases of a sum. What multiplies here is the cases of every
     *  sum the names cross, and each way is a row composed whole; a search reaching this goes no
     *  further and is carried out with the figure. */
    WAYS_UNDER_THE_CASES_TRIED(8),

    /** How many ways a search looks along where conditions on the way to a border came out one of
     *  several ways, each a row is composed along whole. Every way of taking their open
     *  alternatives together where they are no more than this; past it, each open alternative
     *  once beside the others' first ({@link OneOfEach}), and the way looked along whole after
     *  them, which narrows by none of them and is said to have been. */
    WAYS_A_WAY_IS_LOOKED_ALONG(16),

    /** How many alternatives of those conditions are taken in, one beside another, to find the
     *  ways that are open. The walking beside the looking: an alternative that closes against what
     *  was taken before it is looked at and is no way to compose along, and costs a putting
     *  together of what is asked and not a row. A walk this stopped proves nothing closed. */
    CHOICES_ON_A_WAY_LOOKED_AT(4096),

    /**
     * How many values of the numbers of the input a statement about an answer names are tried, each
     * with the answer composed for it.
     *
     * <p>A pair and not a number: what suits the way for one number need not suit the answer, so
     * each value is tried by composing the answer for it, and the first pair every part of which
     * composed is the one taken. A search that went through every pair and found none says the
     * statement was composed against nothing; one that was ended here says this was why, and that a
     * pair past it was not looked at.
     */
    PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED(8),

    /**
     * How many choices of a value for each of the input's numbers a statement names are looked at
     * to find the pairs above.
     *
     * <p>The looking beside the trying, held apart from
     * {@link #PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED} for the reason
     * {@link #PLACES_A_PAIR_IS_LOOKED_AT} is held apart from its own: a choice the way refuses a
     * value of is looked at and is no pair to compose an answer for, and costs a question of the
     * region and not a composing. Counted by what is looked at, whether or not it came to a pair,
     * so that the walk is bounded and not only what it finds.
     */
    CHOICES_OF_INPUT_NUMBERS_LOOKED_AT(256),

    /** How many places along a line a pair is tried at, which is places the walk offered and not
     *  places it went past. What it costs to step over a place the anchored position may not stand
     *  at is {@link #PLACES_A_PAIR_IS_LOOKED_AT}. */
    PLACES_A_PAIR_IS_TRIED_AT(64),

    /**
     * How many places of that line are looked at to find those.
     *
     * <p>The walking beside the trying, held apart from {@link #PLACES_A_PAIR_IS_TRIED_AT} for the
     * reason {@link #PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT} is held apart from its own: a place
     * the line holds that the declarations refuse the anchored position, or that a rule holds it
     * away from, is walked through and is no pair to try.
     */
    PLACES_A_PAIR_IS_LOOKED_AT(512),

    /** How many steps a walk over the positions of a form may take. A run without an end is not
     *  walked to the end at any length. */
    STEPS_A_SEARCH_MAY_TAKE(200_000),

    /** How many assignments of one parameter's positions a search composes. A bound on the search
     *  and not on any one position. */
    ASSIGNMENTS_A_SEARCH_COMPOSES(256),

    /** How many values of a progression nothing bounds are tried. */
    VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED(16),

    /** How many levels past the one a side starts from are asked for. */
    LEVELS_A_SIDE_IS_ASKED_AT(8),

    /** How many numbers, from one up, are tried as a divisor of a level a product is asked at.
     *  The pairs of the divisors not tried are not asked, and the walk is carried out with the
     *  figure. */
    DIVISORS_OF_A_PRODUCT_TRIED(4096),

    /** How many values of the divisor are tried for a remainder an input's number leaves of
     *  another's, nearest nought first. The dividends of the divisors not tried are not asked, and
     *  the walk is carried out with the figure. */
    DIVISORS_OF_A_REMAINDER_TRIED(1024),

    /** How many remainders, from nought up, are tried as the part of a level that a remainder of a
     *  form takes beside the numbers added to it. The remainders not tried are not asked, and the
     *  walk is carried out with the figure. */
    REMAINDERS_A_SUM_IS_TRIED_AT(64),

    /**
     * How often a walk re-reads the rules with the positions it has fixed.
     *
     * <p><b>Reaching it omits no work, which is why nothing carries it.</b> Past this the walk goes
     * on against what the rules left before anything was fixed, which is a wider box and is sound:
     * it offers assignments the narrowing would have skipped and skips none the narrowing would
     * have kept. So a search that met this has still tried everything it would otherwise have
     * tried, and the last step is deliberately outside the figure.
     *
     * <p>Which makes an empty channel the right answer here and not a hole. Handed to an account,
     * it would say a point is open for a figure somebody could raise — of a search that gave up
     * nothing. The others are named beside their carriers; this is named beside the reason it has
     * none.
     */
    TIMES_THE_RULES_ARE_ASKED_AGAIN(2_000),

    /** How many values of one position on the way to a border are tried. Its outcome is not a
     *  composing that stopped: the row is composed, and what was not composed against is one
     *  condition on the way ({@link ReachabilityGap}). */
    VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT(8),

    /**
     * How many places of the run such a position stands on are looked at to find those values.
     *
     * <p><b>Beside the one above and not the same figure.</b> That one bounds the values put to the
     * rest of the question; this one bounds the walking done to reach them. They were one number
     * while every place the run held was a value to try — and they are not, because what the
     * declarations leave the position and what a rule holds it away from take places out of the
     * middle of a run without ending it.
     *
     * <p>Raising them does different things. Raising the first tries more of what was found;
     * raising this one looks further for something to find. A reader told the first where this one
     * stopped the walk is sent to raise a number that changes nothing, which is what one figure
     * standing for both comes to.
     *
     * <p>Wider than the first for the same reason: a stretch every narrowing refuses is walked
     * through and costs this and not that. Needed at all because a run with no end whose values are
     * all refused is otherwise a walk nothing stops.
     */
    PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT(64),

    /**
     * How many assignments of the numbers the conditions on the way to one point name a row is
     * composed for, to learn whether one composes.
     *
     * <p>Its own figure and not either of the two above. Those bound the values of one position
     * the walk tries, and composing is asked of an assignment of every position at once — so how
     * many times it is asked grows as their product, and a value of each composes a location as
     * expensive as the containers the numbers are written into. Spent over every condition on the
     * way to the point, and not afresh for each: a condition placed with others and then on its own
     * asks of the same allowance, so splitting a search is no way past it.
     *
     * <p>Its outcome is the outcome of the two above: the row is composed, and what was not
     * composed against is one condition on the way ({@link ReachabilityGap}).
     */
    ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR(64),

    /**
     * How many values a point is tried with after a row composed for one of them does not stand
     * there.
     *
     * <p>Its own figure and not {@link #PLACES_A_PAIR_IS_TRIED_AT}. That one bounds how many places
     * along a pair's line are walked, which is the geometry of the item; this one bounds how many
     * values a position is asked for after the whole row was built and read back at the point, and
     * what it spends is one value apiece.
     *
     * <p>Nor {@link #VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT}, which is about getting past a
     * condition on the way to the border with the row already composed. The question here is the
     * point itself, asked after the one thing that answers it.
     *
     * <p>One per value and never one per row. A value may be built into several rows — one for each
     * way the dependencies are stood in — and all of them are put to the point before the value is
     * counted as tried. Were it charged per row, a point with more ways to stand its dependencies
     * in would be allowed fewer values than one with fewer.
     *
     * <p><b>So this stops no search either, and what it stops carries it.</b> Each search ran to
     * the end of what it was handed and said what it found; this says the values it was handed were
     * fewer than the point had, which is the answer being over less than the point
     * ({@code Attempt.Limited}). Held nowhere, the figure would be spent on a point whose report
     * says a search had everything and reached nothing.
     *
     * <p><b>And only where it took a value away.</b> Whether there was another value to try is the
     * realizer's answer and not the count's: a point with exactly as many values as this allows is
     * one where every value was tried and nothing was given up, and a figure named there is a
     * number an author raises to be told the same thing. So the asking ends by asking once more —
     * for a value and not for a row, which spends nothing — and what that answer was short of is
     * what the point is said to be short of, this figure or a population this compiler writes some
     * of ({@code Attempt.Unexhausted}).
     */
    VALUES_A_POINT_IS_TRIED_WITH(8),

    /** How many paths through one body a reading of its decision takes. What it had read is carried
     *  out with the figure ({@link DecisionReading.Enumeration.StoppedAtAFigure}), so the rules it
     *  did not reach are neither covered nor gaps. */
    PATHS_OF_A_DECISION_READ(4096),

    /**
     * How many conditions the reading of one body's decision takes into what the declarations
     * leave of the input, in all, asking whether some input takes its ways — every way joined,
     * every way the reading ends at, and every way a proof is said of fewer conditions in.
     *
     * <p>What it counts is the work. Each condition taken in is a region narrowed and asked whether
     * anything is left, which is what a proof costs; the ways asked are as many as the ways joined,
     * which double along a chain, and one way's walk looks at as many alternatives as
     * {@link #CHOICES_ON_A_WAY_LOOKED_AT} lets, each taking its conditions in again. A figure on
     * either of those alone leaves their product unbounded.
     *
     * <p>Over the whole reading and not each way, since what multiplies is how many ways are asked.
     *
     * <p><b>Reaching it proves nothing and stops nothing.</b> Past it no condition is taken in and
     * no way is asked, and a way not proved is a way kept: the rules past it are read as rules, and
     * a rule no run takes among them is what the reading of reach says of it, as it would be with
     * no proof at all.
     */
    CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE(4096),

    /**
     * How many readings of one condition the reading of what it means makes: one per application
     * of a closure handed one of the values a container was written with, and one per case of a
     * value chosen by cases that a comparison is split into.
     *
     * <p>Counted down the tree and not across it. Each reading is of one condition, read once for
     * every application of every closure it is in and for every case of each side it compares, so
     * what multiplies is the nesting and what is counted is the product along one way down — and
     * so what one condition comes to does not turn on how many others beside it were read first.
     *
     * <p>Not an {@code if} a comparison is read through. Its arms are read only where a run takes
     * them, so the ways down a chain of them are the ways a run can go, and one of those may pass
     * as many of them as the chain is long while the ways beside it end at the next; the product
     * along it counts ways that are not there. What bounds those is the count in all
     * ({@link #TOTAL_READINGS_OF_ONE_CONDITION}).
     *
     * <p><b>Reaching it gives the part up and says so.</b> A part that would be read more times
     * than this is not read one by one at all, and is carried out as a part nothing read, naming
     * this as why ({@link souther.compiler.meaning.WhyUnread.MoreReadingsThanAreMade}): a reader is
     * told that the compiler declined the work, and never that the model states nothing there.
     *
     * <p>And the same count bounds what a quantifier asks of an element, taken apart into the ways
     * an element may meet it: the ways no element meets are proved closed and not counted, and
     * past this many open ones the quantifier is not taken into a row's words at all and says so
     * ({@link souther.compiler.meaning.WhyNotTaken.MoreWaysThanAreRead}) — the meaning was read
     * and a row has the words, so neither the reading nor the domain is named.
     */
    READINGS_OF_ONE_CONDITION(256),

    /**
     * How many readings the reading of what one condition means makes in all: every case, value
     * and application it is split into, along every way down and under every rule tried, counted
     * together.
     *
     * <p>Beside {@link #READINGS_OF_ONE_CONDITION} and not in place of it. That one is the product
     * along one way down, so ways that each stay under it can come to more than it in all — a
     * value chosen by cases holds the conditions that chose it, and a helper called on what the
     * last call answered reads every condition before it again, once more on each way. This one
     * is what bounds that, and the only figure the arms of an {@code if} a comparison is read
     * through are held to: an arm no run takes is not read and not counted.
     *
     * <p><b>Reaching it gives the part up and says so</b>, as the other does: the part is carried
     * out as one nothing read, naming this as why
     * ({@link souther.compiler.meaning.WhyUnread.MoreTotalReadingsThanAreMade}). Counted before a
     * split is read, so a reading that stops here never built the readings it stopped short of.
     */
    TOTAL_READINGS_OF_ONE_CONDITION(512),

    /**
     * How many parts the statement one step of a reading concludes comes to, as it is held: every
     * part it holds counted as many times as it holds it, however many of them are one value.
     *
     * <p>Beside the readings and not in place of them. A reading stated more than once — a
     * condition where it holds and denied where it does not, the arms of a match each beside the
     * denial of every arm before it — makes a statement that grows with how deep such steps stand
     * inside one another, so a few readings can come to more parts than any figure.
     *
     * <p>What is held and not what a reader of it does. A reader walks a statement as it is held,
     * and so walks no more of it than this; except a count of statements, which is held as the
     * statements and the counts it admits, each statement once, and which a reader that takes it
     * apart into its choices walks as {@link #PARTS_THE_CHOICES_OF_A_COUNT_COME_TO} bounds.
     *
     * <p><b>Reaching it gives the step up and says so.</b> The step is concluded as a part nothing
     * read, naming this as why ({@link souther.compiler.meaning.WhyUnread.MorePartsThanAreConcluded}).
     * Counted at each step as it is concluded, so a step is made of parts each within the figure;
     * what the step itself builds before it is counted is not bounded by this.
     */
    PARTS_A_DERIVATION_CONCLUDES(4096),

    /**
     * How many parts the choices of which of some statements hold come to written out, every count
     * one reader is handed together, for a reader that takes counts apart into those choices
     * ({@link souther.compiler.meaning.CountsWrittenOut}).
     *
     * <p>Beside {@link #PARTS_A_DERIVATION_CONCLUDES} and not in place of it. That one bounds what
     * a step states, and a count of statements is stated as the statements and the counts it
     * admits, each statement once. Written out as choices, every choice names every statement it
     * needs, so exactly one of {@code n} is {@code n} choices of {@code n} statements — and what a
     * reader that needs the choices walks grows with that and not with what is stated. This bounds
     * that walk: what every count one reader is handed comes to together, and not each count on
     * its own, so a statement holding several counts is held to it once.
     *
     * <p><b>Reaching it gives the choices up and says so.</b> The reader is handed none, and takes
     * the count as it takes a part it could not see into, naming this as why.
     */
    PARTS_THE_CHOICES_OF_A_COUNT_COME_TO(1 << 16),

    /**
     * How many parts of a disjunction one reading of a condition takes alone, to know which of them
     * a path leaves: every part, however deep inside another part it stands, counted against one
     * figure for the reading.
     *
     * <p>Counted across the nesting and not per disjunction. A disjunction of two parts never
     * reaches a figure of its own; what grows is how many times over the nesting takes it — a
     * value chosen by cases and read in a condition carries the condition that chose it, so each
     * helper called on what the last one answered puts every condition before it into the next.
     *
     * <p><b>Reaching it gives the disjunction up and says so.</b> A part not taken may be the one
     * that leaves nothing, so neither a part left alone nor none left is taken from the parts that
     * were, and the disjunction is carried out as one a path did not take in, naming this as why
     * ({@link souther.compiler.meaning.WhyNotTaken.MoreAlternativesThanAreTried}): an arm under it
     * is left unsettled, never shown unreached on a search that did not finish.
     */
    ALTERNATIVES_A_PATH_TRIES(1024),

    /**
     * How many steps a statement of several relations is read in, to say where each of its lines
     * decides.
     *
     * <p>A step is one statement built out of others: a quantifier said with a part about no
     * element of it outside, the statement as its parts come out one at a time
     * ({@link souther.compiler.meaning.WhereEachLineDecides}), which ways its parts can come out
     * together; and, for each line, the statement with the line held against it with the line
     * failing, and what that is left as at each part the cases are taken apart on. Counted once for
     * the statement and once for each line on its own, so what one line spent decides nothing about
     * another. What it bounds is a statement whose parts, every way they come out, leave it as a
     * different statement each time — which is as many as the ways, and doubles with each part.
     *
     * <p><b>Reaching it gives the cases up and says so.</b> The line is where the statement turns,
     * said for cases nobody took apart
     * ({@link souther.compiler.meaning.DecidingCase.Cases.NotTakenApart}), and where rows on both
     * sides of the line reach that, the line is not worked out
     * ({@link souther.compiler.inputs.BlockReason.WhereALineDecidesNotWorkedOut}) — never owed rows
     * where the statement may turn nothing, and never dropped for a proof nobody finished.
     */
    STEPS_A_STATEMENT_IS_READ_IN(1 << 17),

    /**
     * How many cases where a line of a statement of several decides are taken apart, where they are
     * more than are said one by one.
     *
     * <p>Past how many cases are said one by one, the cases are said as one condition and kept
     * beside it ({@link souther.compiler.meaning.DecidingCase}), for a reader to ask whether the
     * line decides in any of them. What this bounds is the taking apart: each case is a way the
     * statement's other parts come out, and finding them walks every way the parts can come out
     * once for each case found. And how many of them are asked: cases kept as choices rather than
     * written out are as many as the ways of choosing one, counted before any is asked, and past
     * this figure none is.
     *
     * <p><b>Reaching it gives the cases up and says so.</b> The condition is kept, said for cases
     * nobody took apart ({@link souther.compiler.meaning.DecidingCase.Cases.NotTakenApart}).
     * Where rows on both sides of the line reach the condition, which is all that says where the
     * cases hold, the line is not worked out in them
     * ({@link souther.compiler.inputs.BlockReason.WhereALineDecidesNotWorkedOut}) — never owed
     * rows where the statement may turn nothing, and never dropped for a proof nobody finished.
     */
    CASES_A_LINE_IS_TAKEN_APART_INTO(256),

    /**
     * How many steps the cases one case of where a line of a statement of several decides was said
     * for are taken through, asking whether a row stands on each side of the line in them: each
     * alternative chosen and each part asked.
     *
     * <p>Every step counted, and not the questions alone. A question is the way to the line with
     * what one case has chosen so far taken in, and a case chosen part by part is asked after each
     * part, so that a part leaving no row on one side settles every case chosen past it. Choosing
     * among alternatives asks nothing of its own, and alternatives below alternatives are as many as
     * the product of them; counted by the questions, a choosing that asks nothing — of cases nobody
     * took apart, or past the last question allowed — would run as far as that product. Counted for
     * each case said as one on its own, so what one of them spent decides nothing about another.
     *
     * <p><b>What the asking costs, and not how many cases there are.</b> How many cases are asked
     * is {@link #CASES_A_LINE_IS_TAKEN_APART_INTO}'s, counted before any is. Which of them the line
     * decides in is asked, and not whether some one does, so where every case divides rows every
     * case is chosen to the end, and what that costs is a step for each alternative and each part
     * on the way to each case. Cases that share what they begin with, as the cases of a statement's
     * parts do, take about four steps each, and this lets that many be asked of as many cases as
     * are taken apart. Cases each chosen through more parts than that, sharing less, take more
     * steps than that, and are where the line can come out not worked out at this figure.
     *
     * <p><b>Reaching it gives that case up and says so.</b> Its cases are neither ones the line
     * turns in nor ones it turns nothing in, so they are where the line was not worked out
     * ({@link souther.compiler.inputs.BlockReason.WhereALineDecidesNotWorkedOut}), beside whatever
     * the line's other cases showed.
     */
    CASES_A_LINE_IS_ASKED_IN(1024),

    /**
     * How deep a construction plan descends.
     *
     * <p><b>Reaching it stops no search: what it shortens is the plan.</b> The composing runs
     * against a plan that has no positions below the figure, so the answer it comes to is its own —
     * every candidate refused, or nothing composed — and what this adds is that the answer is about
     * fewer positions than the value has. The two are carried side by side
     * ({@code Attempt.Limited}), because neither follows from the other.
     *
     * <p>So this has no word of its own. A search that stopped comes back saying so, and a reader
     * may read which budget from that; nothing stopped here, and asking these for a word is what
     * refuses to answer.
     *
     * <p>Where the plan is short of a position the caller asked something at, there is no search at
     * all: a row composed against such a plan is one the caller's own value is missing from, and
     * the plan says so instead of handing one back.
     */
    DEPTH_A_CONSTRUCTION_PLAN_DESCENDS(8),

    /**
     * How many of the numbers a set admits are tried before one of them is built for.
     *
     * <p>A set of numbers is what a class of a number asks a value to read as, and one number of it
     * failing says nothing about the rest: the second of February is a date nothing writes and the
     * thirtieth of a month is one that is written, and both are in the set a rule about months at
     * or after February leaves. So an account walks the numbers it can build for and stops at the
     * first that builds.
     *
     * <p><b>This is what it says when it ran out.</b> Raise it and the numbers past it get tried,
     * which is what makes the word one an author can act on — and what it must never become is the
     * sentence that nothing writes a value in the set, which is a claim about the model that a walk
     * stopped short of the set cannot make.
     *
     * <p>Not spent where the set was walked to its end. A set whose numbers were all tried is one
     * this compiler gave nothing up on, and a figure named there is a number an author raises to be
     * told the same thing.
     */
    NUMBERS_OF_A_SET_TRIED(8),

    /**
     * The most code points of a class a string is asked to hold up to which every way of writing a
     * string holding that many is tried.
     *
     * <p>A string is written by choosing how many code points of each kind it holds, and every
     * number asked of it is a sum of those. Up to this figure every choice is looked at, so a group
     * of counts none of them meets is a group no string answers and is said so. Past it the choices
     * looked at are the ones the numbers asked for and the differences between them suggest, and
     * what that finds nothing in is a string this compiler did not write.
     *
     * <p><b>This is what it says when a search past it found nothing.</b> Raise it and the whole of
     * the choices is looked at for larger counts, which is what makes the word one an author can act
     * on.
     */
    CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL(12),

    /**
     * How many code points past a count a string the type admits is looked for.
     *
     * <p>A string the rules admit of the position — one of a format, or of lengths the rules leave —
     * is offered before one written plainly, and the number of code points it is looked for at is
     * the count asked for and a few more, since a string holding that many of a class is as long
     * and may be longer by the whitespace and separators beside them. A string longer than that is
     * not looked for, and what was not found among those is what this stops.
     */
    CODE_POINTS_BEYOND_A_COUNT_A_STRING_IS_LOOKED_FOR(2),

    /**
     * How many runs one row's exchange for a row that gets further into the body may make.
     *
     * <p>Counted in runs: whether a row got further is what only the behavior says, so every row
     * the exchange looks at costs a run, while a candidate the model refuses costs only its
     * composing. The run of the row being exchanged counts too — it is work done to decide between
     * rows, and a row run once costs nothing the second time.
     *
     * <p>Over the whole exchange and not each guard or each way past one. What it bounds is what a
     * row costs beyond being found, and a share per guard would be a bound that grows with the
     * body.
     *
     * <p><b>It stops no search for the row, so it has no word.</b> The row the search found holds
     * every pin and goes out whatever this comes to. What reaching it stops is a search for a way
     * past the guard the row stops at, at the first row it would have to run, and that is carried
     * beside the row ({@link RepairShortfall.WayPast.CutShort}) — a way a run was refused on is said
     * as one nobody finished looking for, never as one that holds no row. Reaching it ends nothing
     * by itself: a row run already costs nothing to look at again, so a search with none left goes
     * on as far as rows run before take it.
     */
    RUNS_REPAIRING_A_ROW(16),

    /**
     * How many rows a walk composing a row for a point may hand the choice among the rows that
     * answer, each once: the ones that were run and answered, the ones that were run and did not,
     * and the ones that did not meet what they were composed for.
     *
     * <p>Counted in rows composed and not in runs, because a row that is composed again or does not
     * meet the requirement costs composing and no run, and a walk over every assignment of every
     * parameter multiplies. It stops the walk before a row that answers was found, so the point is
     * one this compiler stopped looking for a row at, and never one no row answers at.
     */
    ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW(64);

    private final int maximum;

    CompositionBudget(int maximum) {
        this.maximum = maximum;
    }

    /** The figure itself. What is done on reaching it is the member's to say. */
    public int maximum() {
        return maximum;
    }

    /** This budget as a figure something stopped at. */
    public Figure figure() {
        return new Figure.Budget(this);
    }

    /**
     * What each counts, in the words a reader meets it in.
     *
     * <p>Written per member rather than derived from the name: the names are written for whoever
     * maintains this list, and a reader of a report is owed a sentence they can act on — and a
     * budget added arrives here as a compile error rather than as a name nobody wrote a sentence
     * for.
     */
    public String counts() {
        return switch (this) {
            case ELEMENTS_A_PROPOSAL_HOLDS -> "how many elements a proposed collection holds";
            case CHARACTERS_A_PROPOSAL_HOLDS -> "how many characters a proposed string holds";
            case PAIRINGS_BUILT_AT_ONCE -> "how many of a map's pairings are built at once";
            case ELEMENTS_A_TOTAL_IS_SPREAD_OVER -> "how many elements a total is spread over";
            case SHAPES_OF_A_TOTAL_OFFERED -> "how many containers are offered for one total";
            case ELEMENTS_A_COUNT_IS_COMPOSED_WITH ->
                    "how many elements a container composed for a count holds";
            case CONTAINERS_A_COUNT_IS_OFFERED -> "how many containers are offered for one count";
            case SHARES_A_COUNT_IS_TRIED_AT ->
                    "how many ways of sharing out a container's elements are tried for a count";
            case COUNTS_OF_KEYS_TRIED ->
                    "how many combinations of how often each key occurs are tried";
            case VALUES_AN_ELEMENT_IS_CHOSEN_AMONG ->
                    "how many values of an element are read for a count";
            case WAYS_DOWN_TO_A_TOTAL_TRIED -> "how many ways down to what a total adds up are tried";
            case WAYS_UNDER_THE_CASES_TRIED ->
                    "how many ways under the cases of a sum a container is written are tried";
            case WAYS_A_WAY_IS_LOOKED_ALONG ->
                    "how many ways a row is looked for along where conditions on the way are"
                            + " one of several things";
            case CHOICES_ON_A_WAY_LOOKED_AT ->
                    "how many alternatives of conditions on the way are looked at to find the"
                            + " ways a row may take";
            case CHOICES_OF_INPUT_NUMBERS_LOOKED_AT ->
                    "how many choices of values for the input's numbers are looked at";
            case PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED ->
                    "how many values of the input's numbers are tried with an answer composed"
                            + " for each";
            case PLACES_A_PAIR_IS_TRIED_AT -> "how many places a pair is tried at";
            case PLACES_A_PAIR_IS_LOOKED_AT -> "how many places along a pair's line are looked at";
            case STEPS_A_SEARCH_MAY_TAKE -> "how many steps a search takes";
            case ASSIGNMENTS_A_SEARCH_COMPOSES -> "how many assignments a search composes";
            case VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED ->
                    "how many values of an unbounded progression are tried";
            case LEVELS_A_SIDE_IS_ASKED_AT -> "how many levels a side is asked at";
            case DIVISORS_OF_A_PRODUCT_TRIED ->
                    "how many numbers are tried as a divisor of a level of a product";
            case DIVISORS_OF_A_REMAINDER_TRIED ->
                    "how many values are tried as the divisor of a remainder an input leaves";
            case REMAINDERS_A_SUM_IS_TRIED_AT ->
                    "how many remainders are tried beside the numbers added to them";
            case TIMES_THE_RULES_ARE_ASKED_AGAIN -> "how often the rules are read again";
            case VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT ->
                    "how many values a position on the way is tried at";
            case PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT ->
                    "how many places of a position on the way are looked at";
            case ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR ->
                    "how many values of the numbers on the way a row is composed for";
            case VALUES_A_POINT_IS_TRIED_WITH -> "how many values a point is tried with";
            case DEPTH_A_CONSTRUCTION_PLAN_DESCENDS -> "how deep a value is built";
            case PATHS_OF_A_DECISION_READ -> "how many paths through one body a decision is read for";
            case CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE ->
                    "how many conditions are taken in asking whether some input takes a way through"
                            + " one body";
            case READINGS_OF_ONE_CONDITION ->
                    "how many times one condition is read, once per value or case";
            case TOTAL_READINGS_OF_ONE_CONDITION ->
                    "how many times one condition is read in all, along every case and value";
            case PARTS_A_DERIVATION_CONCLUDES ->
                    "how many parts what one step of a reading states comes to, written out";
            case PARTS_THE_CHOICES_OF_A_COUNT_COME_TO ->
                    "how many parts the choices of which of some statements hold come to, written"
                            + " out for a reader that takes a count of them apart";
            case ALTERNATIVES_A_PATH_TRIES ->
                    "how many parts of one of several things a path takes alone, to know which of"
                            + " them it leaves";
            case STEPS_A_STATEMENT_IS_READ_IN ->
                    "how many steps a statement is read in, to say where each of its lines"
                            + " decides";
            case CASES_A_LINE_IS_TAKEN_APART_INTO ->
                    "how many cases where a line of a statement decides are taken apart";
            case CASES_A_LINE_IS_ASKED_IN ->
                    "how many steps the cases where a line of a statement decides are taken"
                            + " through, asking whether a row stands on each side of it";
            case NUMBERS_OF_A_SET_TRIED -> "how many of the numbers a class admits are tried";
            case CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL ->
                    "how many code points of a class a string is searched for in full";
            case CODE_POINTS_BEYOND_A_COUNT_A_STRING_IS_LOOKED_FOR ->
                    "how many code points past a count a string is looked for";
            case RUNS_REPAIRING_A_ROW -> "how many runs looking for a row that goes further may make";
            case ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW ->
                    "how many rows a walk composing a row for a point hands the choice of a row";
        };
    }

    /**
     * Whether a wider run could go past it: always, since every member is a figure this compiler
     * compared something against and stopped on, which is what a wider run widens.
     */
    public RunSensitivity runSensitivity() {
        return RunSensitivity.MAY_CHANGE;
    }

    /**
     * The figure this one was split off, or null where it was not split off any.
     *
     * <p><b>Because a split figure does not get a word of its own.</b> What a stopped walk says is
     * the walk's answer and the figures are what stopped it, so two figures bounding two halves of
     * one walk come back saying the same thing — one walk cannot say two things depending on which
     * of its own numbers ran out first, and an answer carrying both could not be assembled at all.
     *
     * <p>Said here as data rather than remembered at the place the words are chosen. A figure is
     * split because two things that were one number stopped being one, and the moment after that is
     * exactly when nobody is thinking about which word the new one inherits.
     *
     * <p>Every member answers, so a figure added has to say whether it is one half of another. Read
     * off a default instead, the answer for a new figure would be the one nobody chose.
     */
    public CompositionBudget splitFrom() {
        return switch (this) {
            // The walking beside the trying. Both halves of one walk over a line, and of one walk
            // over the run a position on the way stands on, and of the one over what the input's
            // numbers may be put at.
            case CHOICES_OF_INPUT_NUMBERS_LOOKED_AT -> PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED;
            case PLACES_A_PAIR_IS_LOOKED_AT -> PLACES_A_PAIR_IS_TRIED_AT;
            case PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT ->
                    VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT;
            // And the composing of what that walk tries, which bounds the same walk from the other
            // end: the values it reaches, each composed for.
            case ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR -> VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT;
            case CHOICES_ON_A_WAY_LOOKED_AT -> WAYS_A_WAY_IS_LOOKED_ALONG;
            case ELEMENTS_A_PROPOSAL_HOLDS, CHARACTERS_A_PROPOSAL_HOLDS, PAIRINGS_BUILT_AT_ONCE,
                 ELEMENTS_A_TOTAL_IS_SPREAD_OVER, SHAPES_OF_A_TOTAL_OFFERED,
                 ELEMENTS_A_COUNT_IS_COMPOSED_WITH, CONTAINERS_A_COUNT_IS_OFFERED,
                 SHARES_A_COUNT_IS_TRIED_AT, COUNTS_OF_KEYS_TRIED,
                 VALUES_AN_ELEMENT_IS_CHOSEN_AMONG,
                 WAYS_DOWN_TO_A_TOTAL_TRIED, WAYS_UNDER_THE_CASES_TRIED,
                 PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED,
                 PLACES_A_PAIR_IS_TRIED_AT, STEPS_A_SEARCH_MAY_TAKE,
                 ASSIGNMENTS_A_SEARCH_COMPOSES, VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED,
                 LEVELS_A_SIDE_IS_ASKED_AT, DIVISORS_OF_A_PRODUCT_TRIED,
                 DIVISORS_OF_A_REMAINDER_TRIED, REMAINDERS_A_SUM_IS_TRIED_AT,
                 TIMES_THE_RULES_ARE_ASKED_AGAIN,
                 VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT, VALUES_A_POINT_IS_TRIED_WITH,
                 PATHS_OF_A_DECISION_READ, CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE,
                 READINGS_OF_ONE_CONDITION,
                 TOTAL_READINGS_OF_ONE_CONDITION, PARTS_A_DERIVATION_CONCLUDES,
                 PARTS_THE_CHOICES_OF_A_COUNT_COME_TO,
                 ALTERNATIVES_A_PATH_TRIES, STEPS_A_STATEMENT_IS_READ_IN,
                 CASES_A_LINE_IS_TAKEN_APART_INTO, CASES_A_LINE_IS_ASKED_IN,
                 WAYS_A_WAY_IS_LOOKED_ALONG,
                 DEPTH_A_CONSTRUCTION_PLAN_DESCENDS, NUMBERS_OF_A_SET_TRIED,
                 CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL,
                 CODE_POINTS_BEYOND_A_COUNT_A_STRING_IS_LOOKED_FOR,
                 RUNS_REPAIRING_A_ROW, ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW -> null;
        };
    }
}
