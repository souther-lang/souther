package souther.compiler.coverage;

/**
 * Where a run through one arm is recorded: a number, and the numbering that handed it out.
 *
 * <p>An address and not an identity. What a probed class calls is {@code Probe.hit} with an
 * {@code int}, and what comes back from a recording is that {@code int} — so the number is the
 * vocabulary a run through an arm is written and read in, and it reaches no further. Which arm a
 * reading is talking about is a place in a body ({@link SiteAddress.Arm}), and the two are held
 * apart because they are answered by different things: the numbering hands out an address for the
 * arms it instruments, and a body has arms whether anything instruments them or not.
 *
 * <p><b>Beside {@link ComparisonEmissionSite} and not the same as one.</b> Both are numbers out of
 * one counter, because what records a run is one set of numbers. A number written for an arm and a
 * number written for a comparison are told apart by nothing in the number, so they are told apart
 * by being different types — and which one a number was issued for is the numbering's answer,
 * given once where the number was handed out.
 *
 * <p><b>What it carries is the numbering, and the numbering is a value.</b> Two derivations of one
 * module come to the same numbering, so two addresses of it are the same address. A token minted
 * per construction would have made them two — and one of these is held under answers a store keeps,
 * where an answer that never equals its own recomputation is every reader of it running again on
 * every revision.
 *
 * <p><b>Made by the numbering and by nothing else.</b> There is no way here to pair a number with a
 * numbering that did not hand it out: {@link SiteNumbering#arm} is the only maker, and it refuses a
 * number that numbering never issued and one it issued to a comparison.
 */
public final class ArmProbe implements RunSite {

    private final NumberingIdentity numbering;

    private final int raw;

    ArmProbe(NumberingIdentity numbering, int raw) {
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
                || (other instanceof ArmProbe that
                        && raw == that.raw && numbering.equals(that.numbering));
    }

    @Override
    public int hashCode() {
        return 31 * numbering.hashCode() + raw;
    }

    @Override
    public String toString() {
        return "arm@" + raw;
    }
}
