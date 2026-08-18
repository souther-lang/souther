package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.LinearForm;

/** How a value the affine fragment cannot carry was computed from values it can. */
sealed interface Derivation {

    record Product(LinearForm<FactSubject> left, LinearForm<FactSubject> right) implements Derivation {}

    record Quotient(LinearForm<FactSubject> numerator, long divisor) implements Derivation {}
}
