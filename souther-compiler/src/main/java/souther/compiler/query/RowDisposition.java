package souther.compiler.query;

/**
 * Where one row stands in the account of the answers its behavior's rows owe.
 *
 * <p>Two, because the source says which and there is no third thing it can say. A row states what
 * it expects or is written {@code <?>}; a row whose answer no parse could read is not in this
 * account at all, because it is malformed and the diagnostic that says so owns it.
 *
 * <p>Beside {@link ArmDisposition} and sharing no vocabulary with it. An arm is owed a row and the
 * arm account says whether one goes through it; a row is owed an answer and is owed it whether or
 * not the behavior branches. Nothing takes a row out of this count and nothing leaves it undecided:
 * what is being asked is a fact about the text, settled where the row was read and true whatever
 * becomes of the evaluation.
 */
public enum RowDisposition {

    /** The row states what it expects, so its answer is not owed. */
    MET,

    /**
     * The row is written {@code <?>} and nobody has written what the system answers.
     *
     * <p>The one state a finding is made of and a build can be told to refuse over.
     */
    UNMET
}
