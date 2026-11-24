package souther.compiler.coverage;

/**
 * Where a run entering one walk is recorded: a number, and the numbering that handed it out.
 *
 * <p>A walk is the language's one loop as the tree that runs carries it: a fold walked from the
 * head of its list, or a build growing a collection. Entering it is not going through an arm, and a
 * branch measure counts nothing here; what reads one of these is whatever asks which rows a rewrite
 * of the walk is put to. A row that never entered the walk comes out the same under any rewrite of
 * it, and is not asked.
 *
 * <p>An address and not an identity, for the reasons {@link ArmProbe} is one. Made by the numbering
 * and by nothing else: {@link SiteNumbering#walk} refuses a number it never issued and one it
 * issued to another family.
 */
public final class WalkProbe implements RunSite {

    private final NumberingIdentity numbering;

    private final int raw;

    WalkProbe(NumberingIdentity numbering, int raw) {
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
                || (other instanceof WalkProbe that
                        && raw == that.raw && numbering.equals(that.numbering));
    }

    @Override
    public int hashCode() {
        return 31 * numbering.hashCode() + raw;
    }

    @Override
    public String toString() {
        return "walk@" + raw;
    }
}
