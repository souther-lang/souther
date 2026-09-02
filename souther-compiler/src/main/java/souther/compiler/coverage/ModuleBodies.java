package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.SequencedMap;

/**
 * The behavior bodies of one module, and whose module they are.
 *
 * <p><b>One value because a name read off these says which module.</b> What the numbering and the
 * catalog hand out is a name made of the module, the behavior and where a thing stands, so the
 * module and the trees have to be the same module's. Passed as two arguments they are only as true
 * as the caller made them, and a caller that put one module's name beside another's trees would
 * have the catalog issue names that are true of nothing — names no later check can refuse, because
 * the catalog that issued them is the one being asked.
 *
 * <p><b>Made where the bodies are.</b> The check that produced a module's trees is what knows whose
 * they are, and it is the only thing in the compiler that makes one of these
 * ({@code WhoNamesAComparisonAndWhoAddressesOneTest.onlyACheckPairsAModuleWithItsBodies}).
 * Everything below takes the pair it is given and never takes it apart to build another.
 *
 * <p><b>In the order the module declares them, which is why the type says so.</b> What is numbered
 * off these is where a run is recorded, and the numbering is the walk's order — so a build that
 * walked the bodies in another order would hand out other numbers, and a measuring run reading a
 * recording made by an earlier build would be reading somebody else's places. An unordered copy
 * loses that silently: the map still holds every body, and only the numbers move.
 *
 * @param module whose module the bodies are of
 * @param bodies each behavior of that module, by name, in the order the module declares them
 */
public record ModuleBodies(String module, SequencedMap<String, Core> bodies) {

    public ModuleBodies {
        if (module == null) {
            throw new IllegalArgumentException("bodies are somebody's module's bodies");
        }
        bodies = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(bodies));
    }

    /**
     * Two of these are one where they are the same module's, and the same bodies in the same order.
     *
     * <p><b>The order is part of it, because it is part of what these are for.</b> A map is equal
     * to a map with the same entries however they are arranged — {@code SequencedMap} says so too —
     * and what is numbered off these is where a run is recorded, in the order they are walked. Left
     * to the map's own answer, two of these would be one value and two numberings, and what asks
     * the question is the check's answer saying whether the backend has anything new: a
     * re-check that came back with the bodies in another order would be told there is nothing to
     * emit, over classes whose probe numbers had moved.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof ModuleBodies that && module.equals(that.module)
                && List.copyOf(bodies.entrySet()).equals(List.copyOf(that.bodies.entrySet()));
    }

    @Override
    public int hashCode() {
        return Objects.hash(module, List.copyOf(bodies.entrySet()));
    }

    /** A module with nothing in it, which is what a check that did not finish leaves. */
    public static ModuleBodies none() {
        return new ModuleBodies("", new LinkedHashMap<>());
    }
}
