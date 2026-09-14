package souther.compiler.ast;

/**
 * Which reading a written value is being read under.
 *
 * <p>A value written in a row of an example or of a fake table is a <em>fixture</em>, and the
 * language reads one differently from what the model itself writes (spec §example-evaluable): a
 * fixture leaves an optional field out where the model must write every field, and its {@code [ ]}
 * is the collection its position declares rather than a list. So the reading is not a property of
 * the value that was written — the same characters mean one thing in a body and another in a row —
 * and it is settled once, where the source is read.
 *
 * <p>Held apart from what is read under it, because a construction keeps the answer this settled
 * for it. A value a row names is read as the model's own, and a row that spreads it takes a
 * construction that answered {@link #THE_MODELS_OWN} into a fixture without that construction
 * becoming one — which is what a reading downstream of resolution cannot tell and is why nothing
 * downstream asks.
 */
public enum Reading {

    /** A body, an invariant, an {@code ensures} — what the model writes and is held to. */
    THE_MODELS_OWN,

    /**
     * A fixture: an example row's inputs, a {@code with} value on one, a row's expected value, and
     * a fake table's inputs and outputs (spec §example-fixtures-are-buildable, §example-fakes).
     */
    A_FIXTURE
}
