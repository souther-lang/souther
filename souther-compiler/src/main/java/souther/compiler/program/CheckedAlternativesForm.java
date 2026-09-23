package souther.compiler.program;

import souther.compiler.types.CaseShape;

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
     * An alternative carries something of its own, so each alternative's tag stands under
     * {@code tagKey} (spec §sum-discrimination).
     *
     * <p>A {@link CaseShape#PRODUCT} or {@link CaseShape#UNIT} case carries the tag in the object
     * membership gives it. A {@link CaseShape#WRAPPED} case — a newtype case, a primitive member of
     * an answer — keeps its standalone representation unchanged and places it under
     * {@code contentsKey} beside the tag. Which shape a case has is read from its declaration, not
     * from whether its standalone representation is an object: a newtype over a record writes an
     * object and is still wrapped. Both keys are carried so that a reader writing this form spells
     * neither of them.
     *
     * <p>The two keys differ. A wrapped case writes both into one object, and one key would leave
     * the representation standing where the tag was, which no decoder reads back.
     */
    record Discriminated(String tagKey, String contentsKey) implements CheckedAlternativesForm {

        public Discriminated {
            if (tagKey.equals(contentsKey)) {
                throw new IllegalArgumentException(
                        "the tag and a wrapped case's representation cannot stand under one key: "
                                + tagKey);
            }
        }
    }
}
