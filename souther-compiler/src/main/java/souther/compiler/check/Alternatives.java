package souther.compiler.check;

/** How a reading holds what a choice leaves: the alternatives, or the one product containing
 *  them. Settled per declaration before it is read, so that what a reading answers cannot turn on
 *  how a fold was bracketed. */
enum Alternatives {
    APART,
    MERGED
}
