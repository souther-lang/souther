package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.DischargeRules.Shape;
import souther.compiler.diag.Severity;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How far a predicate travels is a rule about meaning, and no signature answers it: that
 * {@code List.all} holds of any sublist of a list it holds of, and {@code List.contains} does not, is
 * true of what the operations mean and not of what they are declared to be. So it is written down,
 * and a written rule is one that can be written wrong.
 *
 * <p>Wrong in two directions, which fail differently. A rule too narrow loses a discharge: an author
 * guards a predicate and the check reports the construction anyway. A rule too wide accepts one that
 * can abort — the check says a property holds where it does not. The second is the one that matters,
 * and no program that discharges can detect it, being already discharged.
 *
 * <p>So every shape of every rule is answered for here, from both sides: a shape that carries has a
 * program that discharges only because it does, and a shape that does not has the same program over
 * that shape's construction, which must still be reported. What each shape does is written <em>here</em>
 * and not read off the table being held to it — a witness that asks the table what to expect agrees
 * with the table however the table changes, which is no witness at all.
 *
 * <p>What is left is the cells no program can be written for, because the library has no construction
 * of that kind with that shape. Those are named with the reason. A rule whose every carrying shape is
 * one of them reaches nothing, which is worth knowing about a rule — {@code Set.contains} and
 * {@code Map.containsKey} are both that today, and say so here rather than looking witnessed.
 */
class APredicateCarriesExactlyAsFarAsItsRuleSaysTest {

    /** What a construction of a given shape does to a predicate. */
    private enum Travels {
        /** The predicate holds of what was built, so the guard discharges the clause. */
        CARRIES,
        /** It does not, so the clause stands however the container was guarded. */
        STOPS,
        /** The library builds no container of this kind that way. */
        NO_SUCH_CONSTRUCTION
    }

    /** A predicate of the carrying table: the container kind it reads, and how it is written. */
    private record Predicate(String kind, String of, String stated, Map<Shape, Travels> travels) {}

    private static Map<Shape, Travels> travels(Travels permutes, Travels subset, Travels maps,
                                               Travels collapses) {
        return Map.of(Shape.PERMUTES, permutes, Shape.SUBSET, subset, Shape.MAPS, maps,
                Shape.COLLAPSES, collapses);
    }

    /**
     * Every rule, and what every shape does to it. Written out rather than derived: this is the
     * second statement of the rule, and two statements only hold each other up while they are made
     * apart.
     */
    private static final List<Predicate> PREDICATES = List.of(
            // A property of every element survives a reordering and survives dropping elements. It
            // does not survive a mapping — what a mapped element is, the mapping alone does not say.
            new Predicate("List", "List<Int>", "List.all(n -> n >= 1, %s)",
                    travels(Travels.CARRIES, Travels.CARRIES, Travels.STOPS, Travels.STOPS)),
            // Elements distinct by a projection stay distinct in another order and in fewer of them.
            new Predicate("List", "List<Int>", "List.allDistinctBy(n -> n, %s)",
                    travels(Travels.CARRIES, Travels.CARRIES, Travels.STOPS, Travels.STOPS)),
            // That some element holds says nothing once elements can be dropped: the one that held
            // may be the one dropped.
            new Predicate("List", "List<Int>", "List.any(n -> n >= 1, %s)",
                    travels(Travels.CARRIES, Travels.STOPS, Travels.STOPS, Travels.STOPS)),
            // Nor that a particular element is there.
            new Predicate("List", "List<Int>", "List.contains(1, %s)",
                    travels(Travels.CARRIES, Travels.STOPS, Travels.STOPS, Travels.STOPS)),
            new Predicate("Set", "Set<Int>", "Set.contains(1, %s)",
                    travels(Travels.NO_SUCH_CONSTRUCTION, Travels.STOPS,
                            Travels.NO_SUCH_CONSTRUCTION, Travels.STOPS)),
            // A mapping over a map answers one value for each key and leaves the keys alone, so a key
            // being there does survive it — and `MAPS` does not say that, being about the elements
            // and not about what they are held under. Stating it would need a shape that does. The
            // same is true through `Map.updateIfPresent`, which replaces one value and removes no
            // key: what the four words say of a run holding some of each is nothing.
            new Predicate("Map", "Map<String, Int>", "Map.containsKey(\"a\", %s)",
                    travels(Travels.NO_SUCH_CONSTRUCTION, Travels.STOPS, Travels.STOPS,
                            Travels.STOPS)));

    /** How a container of each kind is built from another of the same kind, by shape, or null where
     * the library has no such construction. */
    private static String built(String kind, Shape shape) {
        return switch (kind + "." + shape) {
            case "List.PERMUTES" -> "List.reverse(c)";
            case "List.SUBSET" -> "List.filter(n -> n >= 5, c)";
            case "List.MAPS" -> "List.map(n -> 0, c)";
            case "List.COLLAPSES" -> "List.filterMap(n -> List.get(0, [0]), c)";
            case "Set.SUBSET" -> "Set.filter(n -> n >= 5, c)";
            case "Set.COLLAPSES" -> "Set.map(n -> 0, c)";
            case "Map.SUBSET" -> "Map.filterEntries((k, v) -> v >= 5, c)";
            case "Map.MAPS" -> "Map.mapValues((k, v) -> 0, c)";
            case "Map.COLLAPSES" -> "Map.updateIfPresent(\"a\", v -> v + 1, c)";
            default -> null;
        };
    }

    /**
     * A program that guards the predicate over a container and constructs a value whose invariant
     * states it, from a container built off the guarded one. It discharges exactly when the rule
     * carries the predicate through that construction, and is reported otherwise.
     */
    private static String module(Predicate p, Shape shape) {
        return """
                module demo
                data Bad
                data Held = %s
                    invariant %s
                behavior build : (c: %s) -> Held | Bad constructs Held
                let build (c) = {
                    guard %s
                        else Bad
                    Held(%s)
                }
                """.formatted(p.of(), p.stated().formatted("value"), p.of(),
                p.stated().formatted("c"), built(p.kind(), shape));
    }

    private static long warnings(String src) {
        return Compiler.compileWithWarnings(src).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    /** The operation a predicate names, which is the row of the table it is written against. */
    private static String operationOf(Predicate p) {
        return p.stated().substring(0, p.stated().indexOf('('));
    }

    /** Every row of the table is answered for here, and every answer here is a row. */
    @Test
    void everyRowIsAnsweredFor() {
        Set<String> written = DischargeRules.carryingOperations().stream().map(ValueName::toString)
                .collect(Collectors.toCollection(TreeSet::new));
        Set<String> answered = PREDICATES.stream()
                .map(APredicateCarriesExactlyAsFarAsItsRuleSaysTest::operationOf)
                .collect(Collectors.toCollection(TreeSet::new));
        assertEquals(written, answered,
                "a carrying rule has no program written against it, or the other way round");
    }

    /** A shape that carries discharges the clause, and one that does not leaves it reported. */
    @Test
    void eachShapeCarriesWhatItIsSaidTo() {
        Map<String, String> wrong = new LinkedHashMap<>();
        for (Predicate p : PREDICATES) {
            for (Shape shape : Shape.values()) {
                Travels travels = p.travels().get(shape);
                if (travels == Travels.NO_SUCH_CONSTRUCTION) {
                    continue;
                }
                long warnings = warnings(module(p, shape));
                if (travels == Travels.CARRIES && warnings != 0) {
                    wrong.put(operationOf(p) + " through " + shape,
                            "the guard should discharge the clause and does not");
                }
                if (travels == Travels.STOPS && warnings == 0) {
                    wrong.put(operationOf(p) + " through " + shape,
                            "the clause discharges, and the predicate does not travel there");
                }
            }
        }
        assertEquals(Map.of(), wrong);
    }

    /**
     * And a shape said to have no construction is one <em>the library</em> does not build, not merely
     * one this file has no program for. Both are checked against what the building table says the
     * library builds, so gaining a construction of a kind and shape fails here — the cell above stops
     * being one that can be skipped, and someone has to say what the predicate does through it.
     */
    @Test
    void aShapeSaidToHaveNoConstructionIsOneTheLibraryDoesNotBuild() {
        List<String> wrong = new ArrayList<>();
        for (Predicate p : PREDICATES) {
            for (Shape shape : Shape.values()) {
                boolean builds = DischargeRules.constructionKinds().contains(p.kind() + "." + shape);
                if (builds != (p.travels().get(shape) != Travels.NO_SUCH_CONSTRUCTION)) {
                    wrong.add(operationOf(p) + " through " + shape
                            + (builds ? ": the library builds this and no answer is written"
                                    : ": said to be answerable and the library builds no such thing"));
                }
                if (builds != (built(p.kind(), shape) != null)) {
                    wrong.add(p.kind() + "." + shape
                            + (builds ? ": the library builds this and no program is written for it"
                                    : ": a program is written for what the library does not build"));
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /** Which rules a program can reach at all: one whose only carrying shape has no construction
     * carries nothing, however true it is. */
    @Test
    void whichRulesAnyProgramCanReach() {
        List<String> reaching = new ArrayList<>();
        for (Predicate p : PREDICATES) {
            for (Shape shape : Shape.values()) {
                if (p.travels().get(shape) == Travels.CARRIES) {
                    reaching.add(operationOf(p));
                    break;
                }
            }
        }
        assertEquals(List.of("List.all", "List.allDistinctBy", "List.any", "List.contains"), reaching,
                "these are the carrying rules a program can reach; the rest name a shape no"
                        + " construction of their kind has, and carry nothing");
    }
}
