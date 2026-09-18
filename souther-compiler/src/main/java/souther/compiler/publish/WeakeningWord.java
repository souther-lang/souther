package souther.compiler.publish;

/**
 * What a document calls one weakening.
 *
 * <p>An enum for the same reason every other enumerated field of the report has one: the shipped
 * schema names these words in its own file and is held against this, so a word added here has to be
 * taught to the schema before it can be written.
 *
 * <p>Beside the orders and not beside the writer. What a document calls something is part of what
 * this compiler publishes, which is what this package holds; a vocabulary kept where the writer is
 * would have the order over it reaching up into the writer to say what it is over.
 *
 * <p>Not one constant per {@link souther.compiler.query.Weakening} arm. A weakening that is an
 * observation gone missing writes the {@code Incompleteness} code's own word, because that
 * vocabulary already exists and a second spelling of it would be a second thing to keep in step.
 * What is here is everything else — the facts no observation code covers.
 *
 * <p>{@code ROW_DID_NOT_FINISH} was here and is not. A row that stopped is an observation gone
 * missing like any other, and saying so in this vocabulary as well was the second spelling this
 * class exists to avoid — it also named the row without saying which source it is in, so two rows
 * were one. It writes {@code row_undecided} now, which is the code the row's own reason carries.
 * The word stays in the schema: a version says what its documents may carry (issue #996).
 */
public enum WeakeningWord {

    /** A row came back and what the behavior answered with could not be read as a case. */
    OUTPUT_CASES_UNREADABLE,

    /** The same at one of the inputs. */
    INPUT_CASES_UNREADABLE,

    /** A row's value at one border was observed and the observation did not come back whole. */
    BORDER_VALUE_UNREADABLE,

    /**
     * The walk arrived at no value at one border, so there was none to observe.
     *
     * <p>Its own word beside the one above. Both leave a point undecided and they are not the same
     * news: a value an observation stopped is one a wider budget keeps, and a place this compiler
     * could not get a value out of is not. Said with one word, a reader acting on the report cannot
     * tell which of the two they are looking at, and the difference is the whole of what the reading
     * beneath it was built to carry.
     */
    BORDER_VALUE_ABSENT,

    /**
     * A row's value at one border was never looked at: the walk to the position could not be taken,
     * or no row came back to walk.
     *
     * <p>One word for the two, because what a reader does about them is the same: both are this
     * compiler unable to look rather than the model putting a value elsewhere. Which of the two it
     * was is said by the reading's own reason underneath, and the sentence the document writes is
     * chosen from that; a second word here would be that taxonomy kept in two places, free to drift
     * apart. They part when what a reader does about them parts.
     *
     * <p>Which is the grouping this vocabulary is for, and not a finer claim about the reasons
     * under a word. {@link #BORDER_VALUE_UNREADABLE} covers an observation a wider run would have
     * kept and one it would meet again, and covers them as one word for the same reason: the code
     * travels underneath. A word here says what happened at the coarseness a reader acts on.
     */
    BORDER_OBSERVATION_UNAVAILABLE,

    /**
     * A row held more readings at one border than a point is tried against, so the readings a point
     * was looked for in are not all the readings there are.
     *
     * <p>Its own word beside the three above, and the one of the four that is not about looking. A
     * value that could not be read and a place that holds none are answers a reading came to; this
     * is a reading nobody made. A consumer acts on it differently for the same reason it acts on
     * {@link #PAIR_SPACE_TRUNCATED} differently: what it is short of is a figure of this compiler's,
     * so running again allowing more is the thing to do about it.
     */
    BORDER_READINGS_NOT_EXHAUSTED,

    /**
     * Nothing here holds a border of this shape against the lines the model puts one step from it.
     *
     * <p>Beside the four above and not among them: those are readings of the rows, and this is a
     * question over rows that were read. What it is short of is a strategy nobody has written, so
     * running again allowing more comes to the same answer — which is what tells a consumer to act
     * on it differently from {@link #BORDER_READINGS_NOT_EXHAUSTED}.
     */
    LINES_BESIDE_A_BORDER_NOT_TRIED,

    /**
     * The rows a border was held against all fall on one side of its line, so they pin no threshold
     * on any line beside it.
     *
     * <p>Its own word beside the one above, because what to do about them differs: that one wants
     * this compiler to grow a strategy, and this one wants a row. A border every point of which has
     * a row never comes back this way, so a consumer meeting it is looking at a border that is
     * short of a row as well.
     */
    A_BORDERS_ROWS_ARE_ALL_ON_ONE_SIDE,

    /**
     * A row was left out of what a border was held against because nothing watched its run.
     *
     * <p>Beside the two above because a run allowing more need not leave the same rows out, and
     * beside {@link #DECISION_RUN_NOT_WATCHED} because the two are about different measures: that
     * one is a run this compiler could not place among the rules of a decision, and this is a row
     * whose reaching a comparison could not be told. A consumer joining them would be told one
     * thing about two.
     */
    A_BORDERS_RUN_NOT_WATCHED,

    /**
     * A line beside a border stands after every row, and no input the two answer differently at is
     * one a row still arrives at the border by.
     *
     * <p>So the two are one line as far as this behavior goes, or the way to the border holds a
     * condition nothing here took in — and which of those it is, is not established. A consumer acts
     * on it as it acts on the rest: what is missing is this compiler's, and no row settles it.
     */
    NO_REACHABLE_DISTINGUISHER_FOR_A_BORDER,

    /** A rule of the model that a reader set aside. */
    RULE_UNREAD,

    /** A position the reading did not get into, so there is no rule to name. */
    POSITION_NOT_READ,

    /** A question the rules raised that nothing answered. */
    QUESTION_UNANSWERED,

    /** A position whose rules nothing enumerated. */
    RULES_NOT_REACHED,

    /**
     * A behavior the model gives a body that the image the run was measured in does not carry.
     *
     * <p>One word for every way that happens: a body its own rules refused, one left out because an
     * implementation it reaches could not be made, and a module nothing elaborated at all. What a
     * measure knows is that nothing read the body, and which route the image took to not having it
     * is no part of what a reader acts on.
     *
     * <p>Said of the behavior. The module's word this replaces was true of a compile that stopped
     * and false of every module whose check was made and whose evaluation image is smaller — and a
     * reader shown it went looking for a module that had failed to compile.
     */
    BODY_NOT_IN_EVALUATION,

    /** The boundary of the behavior could not be worked out, so no measure that reads one could be
     *  finished. Every one of them was asked for and started, which is what tells this from a
     *  measure nobody asked for. */
    BEHAVIOR_BOUNDARY_NOT_DERIVED,

    /**
     * The input of the behavior was not read, so no measure that reads a position of it could be
     * finished.
     *
     * <p>Its own word beside the one above. Both leave every measure that reads the boundary
     * unfinished and they send a reader to different places: the first is a name in this
     * behavior's own declaration that resolved to nothing, and this is a module holding a type
     * nobody could name, which refuses the reading of what any of its behaviors take.
     */
    BEHAVIOR_INPUT_NOT_READ,


    /** The space of combinations was too large to walk to the end of. */
    PAIR_SPACE_TRUNCATED,

    /**
     * A meeting of the body's decisions had more combinations than this build walks, so which of
     * them the rows make was never established.
     *
     * <p>Its own word beside the one above, which is the same figure running out on the other
     * criterion. A consumer raising a limit raises a different one for each, and one word for the
     * two would send it to whichever it guessed.
     */
    MEETINGS_NOT_WALKED,

    /** A row went through an arm this compiler had proven nothing arrives at. */
    PROOF_CONTRADICTED,

    /** Two decisions of one body could not be told apart. */
    ARMS_UNSETTLED,

    /**
     * A row ran and which rule of the body's decision it took could not be told.
     *
     * <p>What it takes away is the claim that a rule nothing was seen taking is a rule no row
     * takes. One word for the shortfalls the reading can meet, since a consumer acts on all of them
     * the same way; which of them it was is the reason beside it.
     */
    DECISION_OF_ROW_UNREADABLE,

    /**
     * A row ran and nothing recorded where it went, so which rule it took is not a question this
     * build can put.
     *
     * <p>Apart from the word above because the two are short of different things: that one is a run
     * in hand the rules could not place, and this is no run to place. What they take away is the
     * same claim, and what a reader looks at to fix them is not.
     */
    DECISION_RUN_NOT_WATCHED,

    /**
     * The ways through a body could not all be written down, so what rules its decision has is not
     * known.
     *
     * <p>Apart from the word above, and a consumer acts on them differently: that one leaves a rule
     * undecided, and this one leaves the account without the rules to be undecided about.
     */
    DECISION_NOT_FULLY_READ
}
