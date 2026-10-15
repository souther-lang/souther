package souther.compiler.coverage;

/**
 * Where a run records which way one condition came out: a number, and the numbering that handed it
 * out.
 *
 * <p>A condition here is a truth a body computes and goes on to use — a comparison, or a value of
 * {@code Bool} one of the language's operations answered. What the run writes down is the same for
 * every one of them, the number and the truth it came to, so there is one kind of place for them
 * and what each one is a place of is the reader's to say.
 *
 * <p>An address and not an identity. What a probed class calls is {@code Probe.condition} with an
 * {@code int}, and what comes back from a recording is that {@code int} — so the number is the
 * vocabulary a run is written and read in, and it reaches no further. Which construct a reading is
 * talking about is {@link souther.compiler.types.ConstructOccurrence}, and the two are held apart
 * because they are answered by different things: the plan hands out an address for the conditions
 * it instruments, and a construct stands where it stands whether anything instruments it or not.
 *
 * <p>Kept as one value rather than as the {@code int} it wraps, so that an address cannot be handed
 * where an identity is wanted. Under one type the two were the same number, and a reading that
 * asked which construct it was looking at got an answer that was true only while every construct
 * the catalog held was one the emitter had numbered.
 *
 * <p><b>What it carries is the numbering, and the numbering is a value.</b> Two derivations of one
 * module come to the same numbering, so two addresses of it are the same address — which is what
 * lets one of these be held under an answer a store keeps and compared with what a recomputation
 * makes of it.
 *
 * <p><b>Made by the numbering and by nothing else.</b> {@link SiteNumbering#outcome} is the only
 * maker, and it refuses a number that numbering never issued and one it issued to an arm.
 */
public final class ConditionOutcomeSite implements RunSite {

    private final NumberingIdentity numbering;

    private final int raw;

    ConditionOutcomeSite(NumberingIdentity numbering, int raw) {
        if (numbering == null) {
            throw new IllegalArgumentException("a place a run is recorded at is one some numbering"
                    + " handed out: " + raw);
        }
        if (raw < 0) {
            throw new IllegalArgumentException(
                    "a place a run is recorded at is a place the emitter numbered: " + raw);
        }
        this.numbering = numbering;
        this.raw = raw;
    }

    @Override
    public NumberingIdentity numbering() {
        return numbering;
    }

    @Override
    public int raw() {
        return raw;
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof ConditionOutcomeSite that
                        && raw == that.raw && numbering.equals(that.numbering));
    }

    @Override
    public int hashCode() {
        return 31 * numbering.hashCode() + raw;
    }

    @Override
    public String toString() {
        return "site@" + raw;
    }
}
