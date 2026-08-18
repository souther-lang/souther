package souther.runtime;

/**
 * A case as Souther identifies it: the module that declares it and the name written there.
 *
 * <p>The name alone is not the case. Two modules may each declare a {@code Denied}, and a behavior
 * answering with either would leave a reader of the name unable to tell which one it was — and a
 * comparison of names would call them the same case. Only the pair tells them apart, which is what
 * the compiler has always said of a type and what a failure carrying one out of a run has to keep.
 *
 * <p>Identity here and presentation elsewhere. What a message shows is a reader's decision — the
 * short name where nothing is ambiguous, the qualified one where something is — and whoever decides
 * it reads this rather than being handed a string that has already chosen.
 */
public record DeclaredCase(String module, String name) {

    public DeclaredCase {
        if (module == null || name == null) {
            throw new IllegalArgumentException("a case is the module that declares it and the name "
                    + "written there");
        }
    }

    /** Both parts, as Souther writes a name that leaves nothing to resolve. */
    public String qualified() {
        return module + "." + name;
    }

    @Override
    public String toString() {
        return qualified();
    }
}
