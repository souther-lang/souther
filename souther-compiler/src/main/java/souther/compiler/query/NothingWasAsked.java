package souther.compiler.query;


/**
 * The build asked for no measurement at all, so this measure was not made.
 *
 * <p>One reason shared by every measure that reads the rows, because it is one fact about the run
 * rather than something each of them found out. A measure that owed its own word for it would be a
 * measure a reader has to know to ask, and what a reader wants to know here is the same whichever
 * measure they are looking at: nobody asked, so nothing was counted and nothing was gone without.
 *
 * <p>Beside the reasons a measure does have of its own, and never in place of one. A behavior no row
 * names says {@code NO_ROWS} at every level that measured, and a line a fork drew says the arms were
 * not asked for — those are what this measure found. This is what happens before any of them
 * (issue #955).
 */
public enum NothingWasAsked implements NotMeasuredReason {
    NOT_ASKED
}
