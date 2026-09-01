package souther.compiler.inputs;

import souther.compiler.check.Carrier;

/**
 * Synthetic orders for a test that describes a term rather than reading one.
 *
 * <p>The compiler's own tests have one of these; this is the same bridge for the tests here, which
 * build a report out of evidence rather than out of a model. A package is what package-private
 * means and a Maven module is not, so a test source set of this package reaches
 * {@link TermOrders}'s constructor while nothing that ships does.
 */
public final class TermOrdersFixtures {

    private TermOrdersFixtures() { }

    /** A term whose value is the number it answers. */
    public static TermOrders itself(NumericTerm term, Carrier carrier) {
        return new TermOrders(term, carrier, carrier);
    }
}
