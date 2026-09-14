package souther.compiler.coverage;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a numbering is, said so that two of them can be held against each other.
 *
 * <p>A run is recorded in bare numbers, and a number means a place only under the numbering that
 * handed it out. So a measure reading a recording made under another numbering is answering about
 * places it was not asked about, and the answer is an ordinary yes or no. What stops that is being
 * able to say two numberings are the same one — and that is neither "the same construction" nor
 * "the same inputs".
 *
 * <p><b>Not the same construction.</b> A numbering is derived on demand and the store recomputes,
 * so a token minted per construction would call one numbering two, and a claim answered against a
 * recording made a moment earlier would be refused for having been made a moment earlier.
 *
 * <p><b>Not the same inputs.</b> That the walk is a function of the bodies is exactly the property
 * a reader takes on trust today; identity by input digest moves the trust one step and leaves it
 * standing. A walk whose order came to depend on something else would hand out different numbers
 * under one digest, and nothing would say so.
 *
 * <p><b>The same address space.</b> Two numberings are one when each number means the same place in
 * the same executable. Both halves: {@link #byNumber} says what number addresses what place, and
 * {@link #executable} says what the code at those places does, because two bodies that do different
 * things are not two views of one measurement however their places line up.
 *
 * <p><b>The hash is kept, and it decides nothing.</b> Comparing two of these walks every place and
 * every body, and an address carries one — so a set of addresses would hash the whole numbering per
 * member. What the number saves is the walking, and where two hashes agree the fields are compared
 * all the same: a hash is what makes an answer quick to reach and never what the answer is.
 */
public final class NumberingIdentity {

    private final String module;

    private final Map<String, ExecutableIdentity> executable;

    private final List<SiteAddress> byNumber;

    private final int hash;

    /**
     * @param module     whose bodies these are numbered from
     * @param executable what each behavior of the module does, by name. A map and not a list: what
     *                   order a module declares its behaviors in is not part of what a number
     *                   means, and where it moves the numbers with it {@code byNumber} moves too
     * @param byNumber   what each number is an address of, the number being the position in the list
     */
    public NumberingIdentity(String module, Map<String, ExecutableIdentity> executable,
                             List<SiteAddress> byNumber) {
        if (module == null) {
            throw new IllegalArgumentException("a numbering is of somebody's module");
        }
        this.module = module;
        this.executable = Map.copyOf(executable);
        this.byNumber = List.copyOf(byNumber);
        this.hash = Objects.hash(this.module, this.executable, this.byNumber);
    }

    /**
     * The numbering the plan of nothing carries: no places, of nobody's module.
     *
     * <p>Whose module is not asked for, and there is no way to say. A numbering of a module named
     * here would be one somebody decided without walking a body — the thing every other door into
     * this value exists to stop — and it would be indistinguishable afterwards from the one the
     * check issued. What has no bodies to walk has none to be named after either.
     */
    static NumberingIdentity forThePlanOfNothing() {
        return new NumberingIdentity(ModuleBodies.none().module(), Map.of(), List.of());
    }

    /** Whose bodies these are numbered from. */
    public String module() {
        return module;
    }

    /** What each behavior of the module does, by name. */
    public Map<String, ExecutableIdentity> executable() {
        return executable;
    }

    /** What each number is an address of, the number being the position in the list. */
    public List<SiteAddress> byNumber() {
        return byNumber;
    }

    /** What number {@code n} is an address of. */
    public SiteAddress at(int n) {
        if (n < 0 || n >= byNumber.size()) {
            throw new IllegalArgumentException(
                    "this numbering handed out no " + n + "; it handed out " + byNumber.size());
        }
        return byNumber.get(n);
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof NumberingIdentity that)) {
            return false;
        }
        // The number first and the fields all the same. Two numberings that hash alike and differ
        // are two numberings, and a reader told otherwise would be reading a run against places it
        // was never near — which is the one thing this value exists to stop.
        return hash == that.hash
                && module.equals(that.module)
                && executable.equals(that.executable)
                && byNumber.equals(that.byNumber);
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return "numbering of " + module + " over " + byNumber.size() + " places";
    }
}
