package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Cardinality;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * How many values a declaration has, given how many the declarations it reaches have.
 *
 * <p>One step and not the answer. What every type has is settled by rising from "no value" until
 * nothing moves, and this is the step that rises: handed what is known so far, it says what this one
 * declaration comes to. Kept apart from the rising so that a wrong answer is one or the other and
 * never both at once.
 *
 * <p>Every arm is an upper bound, and the one an arm may not reach for is
 * {@link Cardinality#NO_VALUE}. A shape this does not decide — a name that resolved to nothing, a
 * type standing for another, a form written for expressions and never for a field — answers
 * {@link Cardinality#UNKNOWN}, because refusing a declaration is what a zero here does and a shape
 * nobody read is no reason to refuse anything. The switch over types carries no {@code default} for
 * the same reason: a form added later stops the build here rather than being swallowed into whichever
 * answer this one happened to give.
 *
 * <p>A position is read where it sits. The rules a record wrote about a field reach the value
 * standing there and are read at that field's own path, which is what makes a list holding at least
 * one a different question from the same list holding none. A value a collection holds is not that
 * position — nothing was written about it there — so the reading is put down at a collection's
 * element and the element is asked about its type alone. What that loses is precision: rules do reach
 * an element, and taking the type's answer gives a collection more distinct values to draw on than it
 * has, which admits where a narrower reading would refuse.
 */
final class CardinalityTransfer {

    /**
     * How far a collection's sizes are enumerated before the answer is given up on.
     *
     * <p>Filling a set from an element with {@code n} values means asking about every size up to
     * {@code n}, and the point of asking is to tell a small number of values from a smaller
     * collection. Past a size nothing in the model asks about, the sum is a number no comparison
     * needs, and stopping is losing precision rather than soundness.
     */
    static final int ENUMERATION_LIMIT = 16;

    private CardinalityTransfer() {}

    /** What {@code def}, declared as {@code named}, comes to under {@code solution}. */
    static Cardinality upperOf(TypeName named, Ast.Def def, Symbols symbols,
                               Map<TypeName, Cardinality> solution) {
        return switch (def) {
            case Ast.UnitData _ -> Cardinality.atMost(1);
            case Ast.SumData sum -> {
                // A case bottoming out is the whole sum bottoming out, so these are added and not
                // multiplied: what has no value adds none, and the sum has none only where every one
                // of them has none.
                Cardinality across = Cardinality.NO_VALUE;
                for (Ast.Name each : sum.cases()) {
                    across = across.plus(known(solution, each.denotes()));
                }
                yield across;
            }
            case Ast.Data data -> ofData(named, data, symbols, solution);
        };
    }

    private static Cardinality ofData(TypeName named, Ast.Data data, Symbols symbols,
                                      Map<TypeName, Cardinality> solution) {
        // Rules that cannot all hold leave nothing to count, and the ends they would have been
        // counted between are gone with them. Asked before the positions, which have nothing to say
        // about a value the declaration as a whole refuses.
        if (FieldDomains.of(named, data, symbols).infeasible()) {
            return Cardinality.NO_VALUE;
        }
        OccurrenceCounts counts = OccurrenceCounts.of(named, data, symbols);
        OccurrenceValues values = OccurrenceValues.of(named, data, symbols);
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        if (data.newtype()) {
            // A newtype is one value under a name, so its value sits where it sits: the rules written
            // on the name are about what the value holds, and the value is at no path of its own.
            Type representation = fields.get("value");
            return representation == null ? Cardinality.UNKNOWN
                    : upperAt(representation, FieldDomains.THE_VALUE, counts, values, symbols,
                            solution, new HashSet<>(Set.of(named)));
        }
        Cardinality across = Cardinality.atMost(1);   // a record of no fields is one value
        for (Map.Entry<String, Type> each : fields.entrySet()) {
            across = across.times(upperAt(each.getValue(), each.getKey(), counts, values, symbols,
                    solution, new HashSet<>()));
            if (across.none()) {
                return Cardinality.NO_VALUE;   // one field with no value settles the record
            }
        }
        return across;
    }

    /**
     * How many values may stand at one position.
     *
     * @param path  where the position sits in the value {@code counts} and {@code values} were read
     *              from
     * @param worn  the names this value is already wearing, so that a newtype reached from inside
     *              itself is answered from {@code solution} rather than unwrapped again
     */
    static Cardinality upperAt(Type type, String path, OccurrenceCounts counts,
                               OccurrenceValues values, Symbols symbols,
                               Map<TypeName, Cardinality> solution, Set<TypeName> worn) {
        return switch (type) {
            case Type.Prim prim -> switch (prim) {
                case BOOL -> Cardinality.atMost(2);
                case INT -> values.wholeValuesAt(path);
                // Spaced too finely to count between two ends, or not spaced at all. A string bounded
                // in length and a date bounded at both ends are finite and are not counted here: what
                // it would take is a reading of each carrier's own values, and nothing asks yet.
                case STRING, DECIMAL, DATE, TIME, DATETIME, INSTANT, RAW -> Cardinality.UNKNOWN;
            };
            case Type.Ref ref -> ofRef(ref, path, counts, values, symbols, solution, worn);
            // A `None` is a value of it whatever it wraps, so this is the one position that is never
            // empty. What it wraps is a value of its own type and nothing was written about it here.
            case Type.OptionOf option -> Cardinality.atMost(1)
                    .plus(ofType(option.element(), symbols, solution, worn));
            case Type.ListOf list -> ofList(list.element(), path, counts, symbols, solution, worn);
            case Type.SetOf set -> ofSet(set.element(), path, counts, symbols, solution, worn);
            case Type.MapOf map -> ofMap(map, path, counts, symbols, solution, worn);
            // Several values carried together, which is a product like a record's fields. Written only
            // inside a computation — a field of one is refused — so nothing in a declaration reaches
            // this.
            case Type.TupleOf tuple -> {
                Cardinality across = Cardinality.atMost(1);
                for (Type each : tuple.elements()) {
                    across = across.times(ofType(each, symbols, solution, worn));
                }
                yield across;
            }
            case Type.Union union -> {
                Cardinality across = Cardinality.NO_VALUE;
                for (TypeName each : union.members()) {
                    across = across.plus(known(solution, each));
                }
                yield across;
            }
            // A type standing for another, a name that resolved to nothing, a function, and the two
            // that only an expression reaches: `Nothing` is what an empty list literal's element is
            // waiting to be told, and `Never` is where an abort leaves off. None of them is written
            // in a declaration, and a count of none read off one would refuse a type on the strength
            // of a form this never decided.
            case Type.Open _, Type.Erroneous _, Type.FnOf _, Type.Nothing _, Type.Never _ ->
                    Cardinality.UNKNOWN;
        };
    }

    /** A name, unwrapped while it is one this value is not already wearing. */
    private static Cardinality ofRef(Type.Ref ref, String path, OccurrenceCounts counts,
                                     OccurrenceValues values, Symbols symbols,
                                     Map<TypeName, Cardinality> solution, Set<TypeName> worn) {
        Cardinality named = known(solution, ref.name());
        if (!(symbols.get(ref.name()) instanceof Ast.Data data) || !data.newtype()
                || !worn.add(ref.name())) {
            return named;
        }
        // The name is not a step of the path: a rule the record wrote about this field reaches what
        // the name wraps, and reading the wrapped type without it would leave a floor written here
        // saying nothing. Both readings bound the same values, so the narrower of them holds.
        Type representation = TypeOps.fieldTypes(data, symbols).get("value");
        return representation == null ? named
                : Cardinality.narrower(named,
                        upperAt(representation, path, counts, values, symbols, solution, worn));
    }

    /** A value a collection holds, which no rule of the collection's own was written about. */
    private static Cardinality ofType(Type type, Symbols symbols,
                                      Map<TypeName, Cardinality> solution, Set<TypeName> worn) {
        return upperAt(type, FieldDomains.THE_VALUE, OccurrenceCounts.NOTHING_READ,
                OccurrenceValues.NOTHING_READ, symbols, solution, worn);
    }

    /**
     * What a collection with nothing to put in it comes to.
     *
     * <p>The empty collection is a value of its own, and a collection of a type nobody can build is
     * that value wherever the rules leave room for it. Where they do not — a size they will not let
     * be none, and nothing to fill it with — there is nothing left for it to be.
     *
     * <p>Reached two ways and answered once. The rules can leave nothing to hold by refusing every
     * size above none, and the element can leave nothing to hold by having no values; the collection
     * comes to the same thing either way, and a reader answering the second on its own would refuse a
     * list of an impossible type that is written empty.
     */
    private static Cardinality withNothingToHold(OccurrenceCounts counts, String path) {
        return counts.mayHoldExactly(path, 0) ? Cardinality.atMost(1) : Cardinality.NO_VALUE;
    }

    private static Cardinality ofSet(Type element, String path, OccurrenceCounts counts,
                                     Symbols symbols, Map<TypeName, Cardinality> solution,
                                     Set<TypeName> worn) {
        if (!counts.mayHoldAtLeast(path, 1)) {
            return withNothingToHold(counts, path);
        }
        Cardinality each = ofType(element, symbols, solution, worn);
        if (each.none()) {
            return withNothingToHold(counts, path);
        }
        long distinct = each.boundOr(-1);
        if (distinct < 0) {
            return Cardinality.UNKNOWN;
        }
        // A set holds each of its element's values once, so a size above how many there are is a size
        // nothing fills. Asked whatever the number, because it is one question and not an
        // enumeration.
        if (!counts.mayHoldAtMost(path, distinct)) {
            return Cardinality.NO_VALUE;
        }
        if (distinct > ENUMERATION_LIMIT) {
            return Cardinality.UNKNOWN;
        }
        Cardinality across = Cardinality.NO_VALUE;
        for (long size = 0; size <= distinct; size++) {
            if (counts.mayHoldExactly(path, size)) {
                across = across.plus(each.choose(size));
            }
        }
        return across;
    }

    private static Cardinality ofList(Type element, String path, OccurrenceCounts counts,
                                      Symbols symbols, Map<TypeName, Cardinality> solution,
                                      Set<TypeName> worn) {
        if (!counts.mayHoldAtLeast(path, 1)) {
            return withNothingToHold(counts, path);
        }
        Cardinality each = ofType(element, symbols, solution, worn);
        if (each.none()) {
            return withNothingToHold(counts, path);
        }
        // A list holds its element's values over again, so length and not the element is what bounds
        // it. Left long enough and the lists are past counting however few values the element has.
        if (counts.mayHoldAtLeast(path, ENUMERATION_LIMIT + 1L)) {
            return Cardinality.UNKNOWN;
        }
        Cardinality across = Cardinality.NO_VALUE;
        for (long length = 0; length <= ENUMERATION_LIMIT; length++) {
            if (counts.mayHoldExactly(path, length)) {
                across = across.plus(each.toThe(length));
            }
        }
        return across;
    }

    private static Cardinality ofMap(Type.MapOf map, String path, OccurrenceCounts counts,
                                     Symbols symbols, Map<TypeName, Cardinality> solution,
                                     Set<TypeName> worn) {
        if (!counts.mayHoldAtLeast(path, 1)) {
            return withNothingToHold(counts, path);
        }
        if (!Type.STRING.equals(map.key())) {
            return Cardinality.UNKNOWN;   // keyed by something this has not read
        }
        // A key is a string and there is no end of those, so a map holding anything at all holds it
        // under more keys than can be counted. Only a map with nothing to hold is finite here, and
        // one that must hold something has no value.
        return ofType(map.value(), symbols, solution, worn).none()
                ? withNothingToHold(counts, path) : Cardinality.UNKNOWN;
    }

    /** What {@code solution} says of a name, which is nothing where it holds no answer for it. */
    private static Cardinality known(Map<TypeName, Cardinality> solution, TypeName name) {
        Cardinality had = solution.get(name);
        return had == null ? Cardinality.UNKNOWN : had;
    }
}
