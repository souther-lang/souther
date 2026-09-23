package souther.compiler.program;

/**
 * The form a set of alternatives travels at a boundary — projected from
 * {@link souther.compiler.check.Boundary.Representation}, which is where it is decided. A reader
 * here has nothing left to work out: whether every alternative carries nothing but which one it is
 * was settled while checking, over every alternative at once, and this is that answer carried
 * rather than reasked from the cases alone.
 *
 * <p>Shared by a named sum ({@link CheckedData.Sum}) and a behavior's answer union
 * ({@link CheckedBoundaryOutput.Cases}), because both are one question asked of two spellings
 * (spec §sum-discrimination) and a projection that gave them two answer types would put the choice
 * back with whoever compares the two.
 */
public sealed interface CheckedAlternativesForm {

    /** Every alternative carries nothing but which one it is, so the value is the tag itself. */
    record Enumeration() implements CheckedAlternativesForm {}

    /**
     * An alternative carries something of its own, so the tag stands under {@code tagKey} beside it
     * (spec §sum-discrimination).
     *
     * <p>A case whose own form is an object takes the tag into it; one whose form is not — a newtype
     * case, a primitive member of an answer — writes its form under {@code contentsKey} beside the
     * tag. Both keys are carried so that a reader writing this form spells neither of them.
     */
    record Discriminated(String tagKey, String contentsKey) implements CheckedAlternativesForm {}
}
