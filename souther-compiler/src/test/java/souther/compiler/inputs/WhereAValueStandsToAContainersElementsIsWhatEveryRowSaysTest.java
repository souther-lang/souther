package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How a value stands to the elements of a container ({@link TermPath#toTheElementsOf}) is what
 * every row says, worked out here apart from {@link TermPath}: each row is one case of the value
 * a path may be narrowed at, a path narrowed to cases the row is not stands nowhere on it, and
 * one that stands somewhere is a chain of steps one is inside another of by being its prefix.
 *
 * <p>Asked of every pair of a value and a container that can be written over a value of three
 * cases and another value beside it: narrowed to one case, to two, or not at all, a container
 * of it, its element, a field of the element, and a field beside the container.
 */
class WhereAValueStandsToAContainersElementsIsWhatEveryRowSaysTest {

    private static final List<String> CASES = List.of("Hospital", "Station", "Depot");

    private static final String ELEMENT = "[*]";

    /**
     * A path as this test writes it: a root, the cases it is narrowed to there or null where it is
     * not narrowed, and the steps after it, an element written as {@link #ELEMENT}.
     */
    private record Written(String root, Set<String> narrowedTo, List<String> steps) {

        /** The path as {@link TermPath} holds it. */
        TermPath path() {
            TermPath at = TermPath.of(root);
            if (narrowedTo != null) {
                at = at.refine(CasesLeft.ofEach(CASES.stream().filter(narrowedTo::contains)
                        .map(leaf -> Refinement.of(new Case.SumCase(symbol(leaf), true)))
                        .toList()));
            }
            for (String step : steps) {
                at = ELEMENT.equals(step) ? at.element() : at.then(step);
            }
            return at;
        }

        /** The steps this stands at on a row where the value is {@code row}, or null where it
         *  stands nowhere there. */
        List<String> on(String row) {
            if (narrowedTo != null && !narrowedTo.contains(row)) {
                return null;
            }
            List<String> out = new ArrayList<>();
            out.add(root);
            out.addAll(steps);
            return out;
        }

        Written then(String... more) {
            List<String> all = new ArrayList<>(steps);
            all.addAll(List.of(more));
            return new Written(root, narrowedTo, all);
        }
    }

    private static TypeSymbol symbol(String leaf) {
        return TypeSymbols.declared(new TypeKey("probe", leaf));
    }

    private static boolean prefix(List<String> of, List<String> in) {
        return of.size() <= in.size() && in.subList(0, of.size()).equals(of);
    }

    /** What every row says of {@code value} and the elements of {@code container}. */
    private static TermPath.ToTheElements everyRowSays(Written value, Written container) {
        boolean inside = true;
        boolean holding = true;
        boolean apart = true;
        for (String row : CASES) {
            List<String> at = value.on(row);
            List<String> c = container.on(row);
            if (at != null) {
                List<String> element = c == null ? null : new ArrayList<>(c);
                if (element != null) {
                    element.add(ELEMENT);
                }
                inside &= element != null && prefix(element, at);
            }
            if (c != null) {
                holding &= at != null && prefix(at, c);
            }
            if (at != null && c != null) {
                apart &= !prefix(at, c) && !prefix(c, at);
            }
        }
        return inside ? TermPath.ToTheElements.INSIDE_ONE
                : holding ? TermPath.ToTheElements.HOLDING_THEM
                : apart ? TermPath.ToTheElements.APART
                : TermPath.ToTheElements.NOT_SHOWN;
    }

    /** The value narrowed every way this writes, and the value beside it. */
    private static List<Written> roots() {
        List<Written> out = new ArrayList<>();
        out.add(new Written("x", null, List.of()));
        for (String one : CASES) {
            out.add(new Written("x", Set.of(one), List.of()));
        }
        out.add(new Written("x", Set.of("Hospital", "Station"), List.of()));
        return out;
    }

    private static List<Written> containers() {
        List<Written> out = new ArrayList<>();
        roots().forEach(root -> out.add(root.then("items")));
        out.add(new Written("y", null, List.of("items")));
        return out;
    }

    private static List<Written> values() {
        List<Written> out = new ArrayList<>();
        for (Written root : roots()) {
            out.add(root);
            out.add(root.then("items"));
            out.add(root.then("items", ELEMENT));
            out.add(root.then("items", ELEMENT, "price"));
            out.add(root.then("beds"));
        }
        out.add(new Written("y", null, List.of("items", ELEMENT, "price")));
        out.add(new Written("y", null, List.of()));
        return out;
    }

    @Test
    void whereAValueStandsToTheElementsIsWhatEveryRowSays() {
        for (Written container : containers()) {
            for (Written value : values()) {
                assertEquals(everyRowSays(value, container),
                        value.path().toTheElementsOf(container.path()),
                        () -> value.path() + " to the elements of " + container.path());
            }
        }
    }

    /** Two paths are one place on every row either stands on where each is the other's prefix
     *  on every row both stand on, and each stands on every row the other does. */
    @Test
    void twoPathsAreOnePlaceWhereEveryRowSaysSo() {
        for (Written one : containers()) {
            for (Written other : containers()) {
                boolean same = true;
                for (String row : CASES) {
                    List<String> a = one.on(row);
                    List<String> b = other.on(row);
                    same &= (a == null) == (b == null) && (a == null || a.equals(b));
                }
                assertEquals(same,
                        one.path().standsAtTheSamePlaceOnEveryRow(other.path()),
                        () -> one.path() + " and " + other.path());
            }
        }
    }
}
