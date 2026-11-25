package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Text;
import souther.compiler.types.Type;

import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What tells two quantities, or two divisions of one, apart is what they are, and not how they
 * are written: two written alike are two where they are two things.
 */
class TwoThingsWrittenAlikeAreTwoWhereTheyAreToldApartTest {

    /** How often a value occurs among a list's elements, and a value held aside written as the
     *  same text, are two numbers and two quantities: what a form is the quantity of
     *  ({@link BorderQuantity#identity}) is its key, which is the terms it weighs. */
    @Test
    void twoQuantitiesWrittenAlikeAreTwo() {
        NumericTerm counted = NumericTerm.Multiplicity.of(TermPath.of("i.xs"),
                TermPath.of("i.xs").element().then("a"));
        assertNotNull(counted, "a field of an element is counted among the elements");
        NumericTerm heldAside = new NumericTerm.ValueOf(TermPath.of(counted.toString()));

        assertNotEquals(QuantityKey.of(LinearForm.atom(counted)),
                QuantityKey.of(LinearForm.atom(heldAside)), "two quantities written " + counted);
    }

    /** A division of strings with the last value below {@code "x|y"} and none above, and one
     *  between {@code "x"} and {@code "y|"}, part the strings in two places. */
    @Test
    void twoDivisionsOfStringsWrittenAlikeAreTwo() {
        Carrier strings = Carrier.ofPrimitive(Type.Prim.STRING);
        Level.OnACarrier xy = new Level.OnACarrier(strings, new Text("x|y"));
        Seam one = new Seam(CutPosition.at(xy), xy, null);
        Seam other = new Seam(CutPosition.at(xy),
                new Level.OnACarrier(strings, new Text("x")),
                new Level.OnACarrier(strings, new Text("y|")));

        assertNotEquals(one.key(), other.key(), one + " and " + other);
    }
}
