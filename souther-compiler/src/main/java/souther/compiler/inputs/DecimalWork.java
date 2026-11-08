package souther.compiler.inputs;

import java.util.List;

/**
 * Something a comparison works out over decimals that a run can stop at for want of room, told so
 * that a row can be asked whether the program gets past it ({@link DecimalOperation#allCompleteAt}).
 *
 * <p>Each is a piece of evaluation and not a number: two that come to the same number are told
 * apart where they are worked out apart, since whether there is room is a fact of how the digits
 * are worked out. An operation of two decimals is one ({@link DecimalOperation}); a walk adding the
 * elements of a list to a seed one at a time is another ({@link DecimalAdditiveWalk}), whose steps
 * are shown to get through together and not as one operation over the total.
 */
public sealed interface DecimalWork permits DecimalOperation, DecimalAdditiveWalk {

    /** The pieces of work, by where they are among those told, this one is worked out after. */
    List<Integer> after();

    /** The same, with the work it is worked out of moved {@code by} places later among those
     *  told. */
    DecimalWork shifted(int by);
}
