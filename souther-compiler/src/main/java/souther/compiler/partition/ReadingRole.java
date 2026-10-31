package souther.compiler.partition;

/**
 * What a reading kept to be taken again does with one piece of the state of a {@link Pullback}.
 *
 * <p>A reading made at one place is taken again at another only where the second would come to the
 * same and leave the same behind. Every piece of state says here which of the two it is a part of,
 * or that it is neither, and a piece of state that says nothing is refused where the state is
 * first asked for ({@link ReadingState}).
 */
enum ReadingRole {

    /** The same at every reading of one Pullback. */
    FIXED,

    /** What a reading may ask after. A reading is taken again only where this holds the same. */
    INPUT,

    /** What a reading may ask after only whether there is one. */
    FLAG,

    /** What a reading may ask after, and is compared only for a reading that did: the aggregates
     *  of the way being read. */
    ASKED,

    /** An input that a reading must also leave as it found it, because what it would have added
     *  is not there when the reading is taken again. */
    GUARDED,

    /** A place a reading adds to where there is one and never asks what is in: compared by
     *  whether there is one, and left as found. */
    WRITTEN,

    /** The rule being tried, which a reading must not have said anything into. */
    TRIAL,

    /** The parts met, which stand for the reading only while they are all still met. */
    LEDGER,

    /** The elements asked of, which a reading's footprint says. */
    FOOTPRINT,

    /** The readings left, which a reading is charged and a reading taken again is not. */
    BUDGET,

    /** Only added to, and never asked after by a reading: what a reading added is still there when
     *  it is taken again. */
    ACCRUES,

    /** Answers worked out once whatever asked, and so the same however they were first asked. */
    CACHE,

    /** The readings kept. */
    MEMO,

    /** A count that tells a reading what it did. */
    COUNTER
}
