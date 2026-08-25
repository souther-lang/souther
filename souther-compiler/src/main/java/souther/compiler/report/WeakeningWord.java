package souther.compiler.report;

/**
 * What a document calls one weakening.
 *
 * <p>An enum for the same reason every other enumerated field of the report has one: the shipped
 * schema names these words in its own file and is held against this, so a word added here has to be
 * taught to the schema before it can be written.
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

    /** A row's value at one border could not be read. */
    BORDER_VALUE_UNREADABLE,

    /** A rule of the model that a reader set aside. */
    RULE_UNREAD,

    /** A position the reading did not get into, so there is no rule to name. */
    POSITION_NOT_READ,

    /** A question the rules raised that nothing answered. */
    QUESTION_UNANSWERED,

    /** A position whose rules nothing enumerated. */
    RULES_NOT_REACHED,

    /** The bodies of the module were not elaborated, so what is inside them was not read. */
    BODIES_NOT_ELABORATED,

    /** The boundary of the behavior could not be worked out, so no measure that reads one was
     *  made. */
    BEHAVIOR_BOUNDARY_NOT_DERIVED,


    /** The space of combinations was too large to walk to the end of. */
    PAIR_SPACE_TRUNCATED,

    /** A row went through an arm this compiler had proven nothing arrives at. */
    PROOF_CONTRADICTED,

    /** Two decisions of one body could not be told apart. */
    ARMS_UNSETTLED
}
