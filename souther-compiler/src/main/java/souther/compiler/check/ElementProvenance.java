package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where the elements of what a binding holds came from, for the bindings an expansion wrote.
 *
 * <p>Written where the operation that says so is removed. A collection operation the library
 * declares as a body is spliced into whatever calls it, and afterwards the tree holds a walk with no
 * name on it — so what its answer held the elements of is a fact only the expansion had, and
 * recognising it again from the walk would read the shape a splice happens to leave.
 *
 * <p>Three relations and not one, because they license different things. Where an operation answers
 * the elements it was given — a {@code filter}, a {@code distinct} — the two bindings hold the same
 * values, so a rule about one is a rule about the other and a reading may walk through. Where it
 * answers what a closure made of them, the values came from there and are not those values: what a
 * rule about them means for the position they came from is not settled by knowing where they came
 * from, and a reading that walked through would put a line at a position whose values are not the
 * ones the rule is about.
 *
 * <p>And where the operation answers exactly one of those per element, the closure's own parameter
 * is named beside the container it walks. That is a stronger statement than where the values came
 * from and a narrower one: it says the answers and the elements correspond, which is what a number
 * over the whole run needs and what a walk keeping some of what it was given does not have.
 * {@link #projectedFrom} is that, and the operation it was proved of is gone by the time anything
 * reads the tree — so it is proved where the operation stands and carried by binding.
 *
 * <p>Bindings and not expressions. A binding tells one occurrence from another, which is what two
 * calls of one operation need, and it survives everything between here and the tree that runs —
 * where an expression does not survive being copied, renamed or rewritten.
 */
public record ElementProvenance(Map<BindingId, BindingId> holding,
                                Map<BindingId, BindingId> deriving,
                                Map<BindingId, BindingId> projectedFrom) {

    /** Nothing was expanded, which is what a body calling no such operation comes to. */
    public static final ElementProvenance NONE =
            new ElementProvenance(Map.of(), Map.of(), Map.of());

    public ElementProvenance {
        holding = Map.copyOf(holding);
        deriving = Map.copyOf(deriving);
        projectedFrom = Map.copyOf(projectedFrom);
    }

    /** The binding whose elements {@code binding} holds too, or null where none does. */
    public BindingId sameElementsAs(BindingId binding) {
        return binding == null ? null : holding.get(binding);
    }

    /** The binding whose elements {@code binding}'s were made from, or null where none was. */
    public BindingId madeFrom(BindingId binding) {
        return binding == null ? null : deriving.get(binding);
    }

    /**
     * The container {@code parameter} is the closure parameter of a one-per-element walk over, or
     * null where it is no such parameter.
     *
     * <p>What this licenses is one answer per element of that container, and nothing about the
     * order. A reader that has it still has to show what the answer is — where it stands in the
     * element it was made from — and that is a question about the expression the closure was, not
     * about this.
     */
    public BindingId projectedFrom(BindingId parameter) {
        return parameter == null ? null : projectedFrom.get(parameter);
    }

    public boolean isEmpty() {
        return holding.isEmpty() && deriving.isEmpty() && projectedFrom.isEmpty();
    }

    /** What an expansion writes down as it goes. */
    static final class Builder {

        private final Map<BindingId, BindingId> holding = new LinkedHashMap<>();
        private final Map<BindingId, BindingId> deriving = new LinkedHashMap<>();
        private final Map<BindingId, BindingId> projectedFrom = new LinkedHashMap<>();

        void holdsTheSameAs(BindingId binding, BindingId container) {
            holding.putIfAbsent(binding, container);
        }

        void derivesFrom(BindingId binding, BindingId container) {
            deriving.putIfAbsent(binding, container);
        }

        /** {@code parameter} is the closure parameter of a walk answering one per element of
         *  {@code container}. */
        void projectsEachElementOf(BindingId parameter, BindingId container) {
            projectedFrom.putIfAbsent(parameter, container);
        }

        ElementProvenance built() {
            return holding.isEmpty() && deriving.isEmpty() && projectedFrom.isEmpty() ? NONE
                    : new ElementProvenance(holding, deriving, projectedFrom);
        }
    }
}
