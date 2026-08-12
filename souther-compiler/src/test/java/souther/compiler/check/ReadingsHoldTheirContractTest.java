package souther.compiler.check;

import souther.compiler.types.Type;

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

    private static Type v(String name) {
        return Type.inferredVar(name);
    }

    /** Two variables and two primitives — enough for one variable to stand twice and for two
     * readings to disagree about what it is. */
    private static final List<Type> LEAVES = List.of(v("a"), v("b"), Type.INT, Type.STRING);

    /**
     * {@code inner} under every constructor a reading carries, one layer at a time, so a type of
     * depth two holds another constructor rather than only a leaf. {@code (List<b>, b)} is the shape
     * an occurs check has to reach through, and a universe of one layer over leaves never builds it.
     */
    private static List<Type> around(List<Type> inner) {
        List<Type> out = new ArrayList<>();
        for (Type t : inner) {
            out.add(Type.list(t));
            out.add(Type.set(t));
            out.add(Type.option(t));
        }
        for (Type l : inner) {
            for (Type r : inner) {
                out.add(Type.tuple(List.of(l, r)));
                out.add(Type.map(l, r));
            }
        }
        return out;
    }

    /** Every reading of one layer over the leaves. */
    private static List<Type> shallow() {
        List<Type> out = new ArrayList<>(LEAVES);
        out.addAll(around(LEAVES));
        return out;
    }

    /** Two layers, over the variables alone — where a constructor holds a variable another position
     * settles. Kept to the variables so every pair of it can be taken. */
    private static List<Type> deep() {
        List<Type> vars = List.of(v("a"), v("b"));
        List<Type> out = new ArrayList<>(vars);
        out.addAll(around(vars));
        out.addAll(around(around(vars)));
        return out;
    }

    /** Every pair of {@code from}, and every triple of its first {@code triplesOf}. */
    private static List<List<Type>> groups(List<Type> from, int triplesOf) {
        List<List<Type>> out = new ArrayList<>();
        for (Type l : from) {
            for (Type r : from) {
                out.add(List.of(l, r));
            }
        }
        List<Type> few = from.subList(0, Math.min(triplesOf, from.size()));
        for (Type a : few) {
            for (Type b : few) {
                for (Type c : few) {
                    out.add(List.of(a, b, c));
                }
            }
        }
        return out;
    }

    private static List<List<Type>> everything() {
        List<List<Type>> out = groups(shallow(), 14);
        out.addAll(groups(deep(), 16));
        return out;
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
        for (List<Type> readings : everything()) {
            Type expected = Readings.of(readings);
            for (List<Type> order : orders(readings)) {
                assertEquals(expected, Readings.of(order),
                        show(readings) + " read as " + show(order));
            }
        }
    }

    /** Reading the same thing again says nothing that was not said. */
    @Test
    void givingOneReadingTwiceSaysWhatGivingItOnceSaid() {
        for (List<Type> readings : everything()) {
            List<Type> twice = new ArrayList<>(readings);
            twice.addAll(readings);
            assertEquals(Readings.of(readings), Readings.of(twice), show(readings) + " given twice");
        }
    }

    /**
     * The answer holds everything the readings settled. Asked of the session that settled them, so
     * what is checked is that its own substitution has nothing left to apply — a fresh session would
     * answer yes about a type that had kept a variable the first one knew the value of.
     */
    @Test
    void theAnswerHasNothingLeftToSettle() {
        for (List<Type> readings : everything()) {
            Readings all = new Readings();
            for (Type reading : readings) {
                all.add(reading);
            }
            Type answer = all.answer();
            assertEquals(answer, all.answer(), show(readings) + " asked twice");
            if (answer != null) {
                all.add(answer);
                assertEquals(answer, all.answer(), show(readings) + " read back into itself");
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
                List.of(v("a"), Type.map(Type.STRING, v("b")), v("b")),
                List.of(Type.tuple(List.of(v("a"), v("a"))),
                        Type.tuple(List.of(Type.list(v("b")), v("b")))),
                List.of(Type.tuple(List.of(v("a"), v("a"))),
                        Type.tuple(List.of(Type.map(v("b"), Type.INT), v("b")))),
                List.of(Type.set(v("a")), Type.set(Type.option(v("b"))), v("b"), v("a")));
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
        assertEquals(Type.tuple(List.of(Type.INT, Type.INT)),
                Readings.of(List.of(twice, Type.tuple(List.of(v("b"), Type.INT)))));
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
