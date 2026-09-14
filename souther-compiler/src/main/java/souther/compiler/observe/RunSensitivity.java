package souther.compiler.observe;

/**
 * Whether a wider run of this compiler could come to a different answer about one shortfall.
 *
 * <p><b>What a wider run is.</b> The same sources, the same compiler build, the same dependencies
 * and the same host, with one or more of the allowances this compiler stops under widened and none
 * of them narrowed. An allowance is a figure this compiler compared something against and stopped
 * on: the steps a row is evaluated for, the depth a recursion may reach, the clock it is held to,
 * the nodes an observation keeps, the combinations a measure walks, the states a pattern is built
 * into. Whether a caller can set the figure today is not the question — several of them are
 * constants — because that is a fact about which knobs exist this month and not about the stop.
 *
 * <p>So the host is not an allowance. The stack running out and the classes failing to link are met
 * again by a wider run on the same machine, and a run on another machine is a different host rather
 * than a wider run of this one.
 *
 * <p><b>The question a producer answers.</b> Did an allowance of this compiler's stop it. That is
 * the whole of it. The other half of the sentence this used to carry — "or did it have no reading
 * for what it met" — is a classification and not this axis, and it was already false of things that
 * answer {@link #UNAFFECTED}: a measure nobody made met nothing and read nothing, and a point where
 * nothing showed a row can be written is not a reading either.
 *
 * <p>So nothing here says what kind of thing it was, and nothing here is a judgment about what a
 * person should do. Both of those belong to the kind beside it, one word at a time. This says only
 * whether measuring the same model again, allowing more, could answer what was not answered.
 *
 * <p><b>And what it does not promise.</b> {@link #MAY_CHANGE} is not that a wider run finishes the
 * measure. It is that the stop that produced this shortfall need not happen again — a reading past
 * one figure may be stopped by the next, and nothing here is contradicted by that. {@link
 * #UNAFFECTED} is the stronger of the two and is the one a reader acts on: no allowance widens it,
 * so a person told to measure again with more would be measuring the same thing twice.
 *
 * <p><b>Not "recoverable" and not "permanent".</b> A shortfall no allowance changes is one a later
 * version of this compiler may well read, and a person may always write the model another way.
 * Both of those are outside what a run is, and a word claiming them would be claiming what nothing
 * here establishes.
 */
public enum RunSensitivity {

    /** An allowance of this compiler stopped it, so a run that allows more need not stop there. */
    MAY_CHANGE,

    /** No allowance stopped it, so every run of this compiler over this model says the same. */
    UNAFFECTED
}
