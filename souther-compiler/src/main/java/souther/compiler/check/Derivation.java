package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.LinearForm;

/** How a value the affine fragment cannot carry was computed from values it can. */
sealed interface Derivation {

    record Product(LinearForm<Term> left, LinearForm<Term> right) implements Derivation {}

    record Quotient(LinearForm<Term> numerator, long divisor) implements Derivation {}
}
