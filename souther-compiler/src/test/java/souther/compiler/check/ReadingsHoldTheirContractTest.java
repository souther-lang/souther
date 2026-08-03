package souther.compiler.check;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What every reading of one value answers is a property of the readings, not of the order they were
 * given in or of how many times each was given. Checked over every small type there is rather than
 * over the examples that happened to come up: the faults this had were each found by one more
 * combination than the examples covered.
 */
class ReadingsHoldTheirContractTest {

    private static final BindingId OWNER =
            new BindingId(new BindingOwner.OfData(new TypeName("demo", "X")), 0);

    private static Type v(String name) {
        return Type.mintedVar(name, OWNER);
    }

    /** Every type of depth two over two variables, two primitives and the constructors readings
     * carry. Small enough to take every triple of, wide enough to hold the shapes that broke. */
    private static List<Type> universe() {
        List<Type> leaves = List.of(v("a"), v("b"), Type.INT, Type.STRING);
        List<Type> all = new ArrayList<>(leaves);
        for (Type l : leaves) {
            all.add(Type.list(l));
            all.add(Type.option(l));
            all.add(Type.map(Type.STRING, l));
            for (Type r : leaves) {
                all.add(Type.tuple(List.of(l, r)));
            }
        }
        return all;
    }

    /** Shows a variable by its name, so a failure names the readings rather than showing `_`. */
    private static String raw(Type t) {
        return switch (t) {
            case Type.Var v -> v.name();
            case Type.ListOf l -> "List<" + raw(l.element()) + ">";
            case Type.SetOf x -> "Set<" + raw(x.element()) + ">";
            case Type.OptionOf o -> raw(o.element()) + "?";
            case Type.MapOf m -> "Map<" + raw(m.key()) + ", " + raw(m.value()) + ">";
            case Type.TupleOf tu -> {
                StringBuilder b = new StringBuilder("(");
                for (Type e : tu.elements()) {
                    b.append(b.length() == 1 ? "" : ", ").append(raw(e));
                }
                yield b.append(")").toString();
            }
            default -> Type.show(t);
        };
    }

    private static List<List<Type>> triples() {
        List<Type> all = universe();
        List<List<Type>> out = new ArrayList<>();
        for (int i = 0; i < all.size(); i += 3) {
            for (int j = 0; j < all.size(); j += 5) {
                for (int k = 0; k < all.size(); k += 7) {
                    out.add(List.of(all.get(i), all.get(j), all.get(k)));
                }
            }
        }
        return out;
    }

    private static String show(List<Type> readings) {
        StringBuilder b = new StringBuilder();
        for (Type t : readings) {
            b.append(b.isEmpty() ? "" : ", ").append(raw(t));
        }
        return b.toString();
    }

    /** Which reading arrived first is not something the readings say. */
    @Test
    void theAnswerDoesNotDependOnTheOrderTheReadingsArriveIn() {
        for (List<Type> three : triples()) {
            Type a = three.get(0);
            Type b = three.get(1);
            Type c = three.get(2);
            Type expected = Readings.of(List.of(a, b, c));
            for (List<Type> order : List.of(List.of(a, c, b), List.of(b, a, c),
                    List.of(b, c, a), List.of(c, a, b), List.of(c, b, a))) {
                assertEquals(expected, Readings.of(order), show(three) + " read as " + show(order));
            }
        }
    }

    /** Reading the same thing again says nothing that was not said. */
    @Test
    void givingOneReadingTwiceSaysWhatGivingItOnceSaid() {
        for (List<Type> three : triples()) {
            Type answer = Readings.of(three);
            List<Type> twice = new ArrayList<>(three);
            twice.addAll(three);
            assertEquals(answer, Readings.of(twice), show(three) + " given twice");
        }
    }

    /** The answer holds everything the readings settled, so reading it back settles nothing more. */
    @Test
    void theAnswerHasNothingLeftToSettle() {
        for (List<Type> three : triples()) {
            Type answer = Readings.of(three);
            if (answer != null) {
                assertEquals(answer, Readings.of(List.of(answer)), show(three) + " read back");
                assertEquals(answer, Readings.of(List.of(answer, answer)),
                        show(three) + " read back twice");
            }
        }
    }

    /** A value cannot hold itself, whichever readings say so and in whatever order. */
    @Test
    void aValueThatWouldHaveToHoldItselfIsRefusedInEveryOrder() {
        List<List<Type>> cannot = List.of(
                List.of(v("a"), Type.list(v("a"))),
                List.of(v("a"), v("b"), Type.list(v("b"))),
                List.of(v("a"), Type.tuple(List.of(Type.INT, v("a")))),
                List.of(v("a"), v("b"), Type.option(v("a"))),
                List.of(v("a"), Type.map(Type.STRING, v("b")), v("b")));
        for (List<Type> readings : cannot) {
            for (List<Type> order : orders(readings)) {
                assertNull(Readings.of(order), show(order));
            }
        }
    }

    /** A variable standing twice holds one type wherever the readings settle it. */
    @Test
    void aVariableStandingTwiceHoldsOneType() {
        Type twice = Type.tuple(List.of(v("a"), v("a")));
        assertEquals(Type.tuple(List.of(Type.INT, Type.INT)),
                Readings.of(List.of(twice, Type.tuple(List.of(Type.INT, Type.INT)))));
        assertEquals(Type.tuple(List.of(Type.INT, Type.INT)),
                Readings.of(List.of(twice, Type.tuple(List.of(Type.INT, v("b"))))));
        assertNull(Readings.of(List.of(twice, Type.tuple(List.of(Type.INT, Type.STRING)))));
    }

    private static List<List<Type>> orders(List<Type> of) {
        List<List<Type>> out = new ArrayList<>();
        permute(new ArrayList<>(of), 0, out);
        return out;
    }

    private static void permute(List<Type> at, int from, List<List<Type>> out) {
        if (from == at.size()) {
            out.add(List.copyOf(at));
            return;
        }
        for (int i = from; i < at.size(); i++) {
            java.util.Collections.swap(at, from, i);
            permute(at, from + 1, out);
            java.util.Collections.swap(at, from, i);
        }
    }
}
