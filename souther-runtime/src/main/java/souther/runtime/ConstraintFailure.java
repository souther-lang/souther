package souther.runtime;

/**
 * A constraint the model declared cannot be broken, broken while the domain ran.
 *
 * <p>Two things in the language state one: a {@code data}'s {@code invariant}, which every
 * construction of that type owes, and a {@code behavior}'s {@code ensures}, which relates what a
 * behavior is given to what it answers. They are not one kind of failure wearing two names — an
 * invariant is about what a value is and belongs to its type, a clause is about what one behavior
 * answers — so each says what it is, and this is what they have in common: a declaration that the
 * model made and the run did not keep.
 *
 * <p>What they share is the destination. Neither is a business case (spec §violation-destination),
 * so neither rides an output sum, and both leave by {@link ConstraintViolation#notHeld}. Sealed so
 * that a third origin is a case somebody writes here rather than one of these two stretched to
 * carry it: {@code InvariantFailure} carrying a behavior name would be a type saying something it
 * is not about.
 */
public sealed interface ConstraintFailure permits InvariantFailure, EnsuresFailure {

    /** What the abort says, and what a boundary reporting one has to work with. */
    @Override
    String toString();
}
