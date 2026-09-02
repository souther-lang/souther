package souther.compiler.coverage;

import java.util.List;
import java.util.Map;

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
 * @param module   whose bodies these are numbered from
 * @param executable what each behavior of the module does, by name. A map and not a list: what
 *                   order a module declares its behaviors in is not part of what a number means,
 *                   and where it moves the numbers with it {@code byNumber} moves too
 * @param byNumber what each number is an address of, the number being the position in the list
 */
record NumberingIdentity(String module, Map<String, ExecutableIdentity> executable,
                         List<SiteAddress> byNumber) {

    NumberingIdentity {
        if (module == null) {
            throw new IllegalArgumentException("a numbering is of somebody's module");
        }
        executable = Map.copyOf(executable);
        byNumber = List.copyOf(byNumber);
    }

    /** The numbering of nothing, which is what a module with no bodies to walk has. */
    static NumberingIdentity of(String module) {
        return new NumberingIdentity(module, Map.of(), List.of());
    }

    /** What number {@code n} is an address of. */
    SiteAddress at(int n) {
        if (n < 0 || n >= byNumber.size()) {
            throw new IllegalArgumentException(
                    "this numbering handed out no " + n + "; it handed out " + byNumber.size());
        }
        return byNumber.get(n);
    }

    @Override
    public String toString() {
        return "numbering of " + module + " over " + byNumber.size() + " places";
    }
}
