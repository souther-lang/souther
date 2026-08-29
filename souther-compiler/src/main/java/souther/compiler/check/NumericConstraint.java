package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.Set;

/**
 * A relation a reading found stated of some values: this form, standing in this relation to nought.
 *
 * <p>What is said and not what it comes to. {@code x < 100} is this; that {@code x} lies between
 * nought and ninety-nine is what taking it into a domain answers, and that answer belongs to the
 * domain it was taken into. So this is the same value wherever it is read, which is what lets it be
 * recorded beside a recipe ({@link Derivation.Chosen}) where a range could not be.
 *
 * <p>Its own type and not one reader's. {@link Conditions} produces these, {@link Predicates} takes
 * them into what is known on a path, {@link Derivation.Chosen} records the ones choosing an arm
 * states, and {@link DerivedNumericFacts} both reads an arm under them and answers with them where
 * a recipe has a relation to state rather than a range. A vocabulary four readers share is not one
 * of their implementations — and it is one type and not two, since a relation a condition wrote and
 * a relation a reading derived go through the same door into a domain and differ in nothing a
 * reader of either could act on.
 */
record NumericConstraint(LinearForm<FactSubject> form, Rel rel)
        implements DerivedNumericFacts.Fact {

    /** The atoms this relation is written over. */
    Set<FactSubject> atoms() {
        return form.coefs().keySet();
    }
}
