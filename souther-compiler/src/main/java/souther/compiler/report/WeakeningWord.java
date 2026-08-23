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
 */
public enum WeakeningWord {

    /** A row came back and what the behavior answered with could not be read as a case. */
    OUTPUT_CASES_UNREADABLE,

    /** The same at one of the inputs. */
    INPUT_CASES_UNREADABLE,

    /** A row stopped before it finished, so what it went through went with it. */
    ROW_DID_NOT_FINISH,

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

    /** A position dropped past the axis limit. */
    AXIS_OMITTED,

    /** The space of combinations was too large to walk to the end of. */
    PAIR_SPACE_TRUNCATED,

    /** A row went through an arm this compiler had proven nothing arrives at. */
    PROOF_CONTRADICTED,

    /** Two decisions of one body could not be told apart. */
    ARMS_UNSETTLED
}
