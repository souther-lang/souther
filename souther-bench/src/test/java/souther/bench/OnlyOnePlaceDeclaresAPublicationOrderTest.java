package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The order a kind of reason is published in is declared in one place, and nowhere else makes one.
 *
 * <p>What the compiler holds is that an order is made inside its own package: the two factories are
 * package-private, so no other part of this compiler can reach them. What that leaves open is a
 * second class in that package making one — and then a kind would have two orders, which is the
 * thing the whole arrangement is against.
 *
 * <p>Read off the call sites rather than off the declarations. A check over the fields of the other
 * classes there would see a field of the order's type and miss an order made inside a method and
 * used from there, which is the same second order with nowhere to see it. What makes an order is
 * calling one of two methods, and this says who calls them.
 */
class OnlyOnePlaceDeclaresAPublicationOrderTest {

    private static final String ORDER = "souther.compiler.publish.CanonicalSelection$Order";
    private static final String AUTHORITY = "souther.compiler.publish.PublicationOrders";

    @Test
    void nothingButThePublicationOrdersMakesAnOrder() throws Exception {
        List<String> made = new ArrayList<>();
        boolean reached = false;
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals(ORDER)
                    && (site.member().equals("overValues") || site.member().equals("overFamilies"))) {
                reached = true;
                if (!site.from().equals(AUTHORITY)) {
                    made.add(site.at());
                }
            }
        }

        assertFalse(made.isEmpty() && !reached,
                "no order is made anywhere, so this is passing for the wrong reason");
        assertEquals(List.of(), made,
                "an order over a kind of reason made outside the one place that declares them,"
                        + " which is how a kind comes to have two orders that agree until one moves");
    }
}
