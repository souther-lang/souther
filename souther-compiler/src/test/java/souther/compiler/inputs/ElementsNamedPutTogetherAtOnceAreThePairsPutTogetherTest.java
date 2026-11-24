package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What several readings of elements by name come to put together at once is what they come to
 * put together two at a time, in order — each slot with the names of all, in the order met — and
 * where the rest add nothing to the first, the first itself.
 *
 * <p>Held against the pairwise putting together written out here, over every order of a few
 * readings that name one element through one name, through two, through a name of another
 * element, and through a name whose element is not known.
 */
class ElementsNamedPutTogetherAtOnceAreThePairsPutTogetherTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);
    private static final ElementsNamed.Slot ITEM = new ElementsNamed.Slot(
            new InputReads.ContainerOf.AtAPosition(TermPath.of("x").then("items")),
            HeldIn.Part.ELEMENT);
    private static final ElementsNamed.Slot LINE = new ElementsNamed.Slot(
            new InputReads.ContainerOf.AtAPosition(TermPath.of("x").then("lines")),
            HeldIn.Part.ELEMENT);

    /** Two at a time, as each slot gets the names of both in the order met. */
    private static ElementsNamed pairwise(ElementsNamed one, ElementsNamed other) {
        if (other.isEmpty()) {
            return one;
        }
        if (one.isEmpty()) {
            return other;
        }
        Map<ElementsNamed.Slot, Set<BindingId>> out = new LinkedHashMap<>();
        one.named().forEach((slot, names) -> out.put(slot, new LinkedHashSet<>(names)));
        other.named().forEach((slot, names) ->
                out.computeIfAbsent(slot, _ -> new LinkedHashSet<>()).addAll(names));
        Set<ElementsNamed.Slot> unnamed = new LinkedHashSet<>(one.unnamed());
        unnamed.addAll(other.unnamed());
        return new ElementsNamed(out, unnamed);
    }

    private static void orders(List<ElementsNamed> left, List<ElementsNamed> so,
                               List<List<ElementsNamed>> out) {
        if (left.isEmpty()) {
            out.add(List.copyOf(so));
            return;
        }
        for (int at = 0; at < left.size(); at++) {
            List<ElementsNamed> rest = new ArrayList<>(left);
            so.add(rest.remove(at));
            orders(rest, so, out);
            so.removeLast();
        }
    }

    @Test
    void everyOrderPutTogetherAtOnceIsThePairsPutTogether() {
        ElementsNamed a = ElementsNamed.of(List.of(new ElementsNamed.Named(ITEM, A)));
        ElementsNamed alsoA = ElementsNamed.of(List.of(new ElementsNamed.Named(ITEM, A)));
        ElementsNamed b = ElementsNamed.of(List.of(new ElementsNamed.Named(ITEM, B)));
        ElementsNamed line = ElementsNamed.of(List.of(new ElementsNamed.Named(LINE, A)));
        ElementsNamed unknown = ElementsNamed.of(List.of(), Set.of(ITEM));
        List<List<ElementsNamed>> all = new ArrayList<>();
        orders(List.of(a, alsoA, b, line, unknown, ElementsNamed.NONE), new ArrayList<>(), all);
        orders(List.of(a, alsoA, ElementsNamed.NONE), new ArrayList<>(), all);
        for (List<ElementsNamed> order : all) {
            ElementsNamed expected = ElementsNamed.NONE;
            for (ElementsNamed each : order) {
                expected = pairwise(expected, each);
            }
            assertEquals(expected, ElementsNamed.allOf(order), order.toString());
            assertEquals(expected.named().toString(), ElementsNamed.allOf(order).named().toString(),
                    "in the order met: " + order);
        }
        assertSame(a, ElementsNamed.allOf(List.of(ElementsNamed.NONE, a, alsoA, a)),
                "the first, where the rest add nothing to it");
    }
}
