package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * The values an element is chosen among, where what is asked of it is read of each whole: every
 * value of each part of it that has only so many, and at each part that is a number the values
 * the statements part its run at.
 *
 * <p>A truth, a case of a sum, a record of such parts and an optional of one are each one of
 * finitely many, so every one of them is read. A number has values without end, and what the
 * statements asked of the element say of it is where they turn over, so the values standing for
 * each run between those places are the ones read ({@code numbersAt}). A part that is neither — a
 * text, a container — has values nothing here chooses among, and an element holding one is not
 * one of these.
 *
 * <p>Written the way the values a run holds are read back, so that what is read of one is what a
 * row holding it would be read as: a name the type wears around another is a construction holding
 * the value under {@code value}, and a case of a sum is its own construction.
 *
 * <p>Nothing here asks whether a value is one the rules admit. What a newtype accepts is the
 * decoder's to say where the row is built, as for every value a composer proposes
 * ({@link Witnesses}).
 */
final class ValuesOfAnElement {

    private ValuesOfAnElement() {
    }

    /**
     * The values listed, and whether they are every value the parts were read at.
     *
     * @param values the values, in the order the declarations write their cases and fields
     * @param all    whether they are every one; false where {@code most} stopped the listing
     */
    record Listed(List<ObservedValue> values, boolean all) {

        Listed {
            values = List.copyOf(values);
        }
    }

    /**
     * As many as {@code most} values of {@code type} standing at {@code at}; null where some part
     * of it is one nothing here chooses values of.
     *
     * @param numbersAt the values a number standing at a position is read at, or null where none
     *                  are chosen there
     */
    static Listed of(Type type, TermPath at, RuleReadingContext reading, int most,
                     Function<TermPath, List<ObservedValue>> numbersAt) {
        List<ObservedValue> out = valuesOf(type, at, reading.source(), most + 1, numbersAt,
                new HashSet<>());
        if (out == null) {
            return null;
        }
        return out.size() > most ? new Listed(out.subList(0, most), false)
                : new Listed(out, true);
    }

    /**
     * Up to {@code most} values of {@code type} standing at {@code at}, or null where some part of
     * it is one nothing here chooses values of, or a type written in terms of itself.
     *
     * <p>None where there is no room for one: what holds this part has used its room up, and the
     * listing above it is the one that says it stopped.
     */
    private static List<ObservedValue> valuesOf(Type type, TermPath at, RuleReadingSource source,
                                                int most,
                                                Function<TermPath, List<ObservedValue>> numbersAt,
                                                Set<TypeSymbol> expanding) {
        if (most <= 0) {
            return List.of();
        }
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        List<ObservedValue> bare = switch (view.shape()) {
            case Shape.Scalar scalar -> scalar.prim() == Type.Prim.BOOL
                    ? List.of(new ObservedValue.Bool(false), new ObservedValue.Bool(true))
                    : numbersAt.apply(at);
            case Shape.Unit unit -> List.of(new ObservedValue.Unit(unit.name()));
            case Shape.Product product -> {
                if (!expanding.add(product.name())) {
                    yield null;
                }
                List<ObservedValue> made = recordsOf(product, at, source, most, numbersAt,
                        expanding);
                expanding.remove(product.name());
                yield made;
            }
            // Each case where it stands under the narrowing to it, which is where what is read
            // of a field of the case is read.
            case Shape.Sum sum -> {
                List<ObservedValue> made = new ArrayList<>();
                for (TypeSymbol each : sum.reaches().cases()) {
                    boolean oneValue = TypeView.of(Type.ref(each), source.inners(),
                            source.symbols(), source.kinds(), source.sums()).shape()
                            instanceof Shape.Unit;
                    List<ObservedValue> ofTheCase = valuesOf(Type.ref(each),
                            at.refine(Refinement.of(new Case.SumCase(each, oneValue))), source,
                            most - made.size(), numbersAt, expanding);
                    if (ofTheCase == null) {
                        yield null;
                    }
                    made.addAll(ofTheCase);
                    if (made.size() >= most) {
                        break;
                    }
                }
                yield made;
            }
            case Shape.Optional optional -> {
                List<ObservedValue> held = valuesOf(optional.element(),
                        at.refine(Refinement.of(new Case.Presence(true))), source, most - 1,
                        numbersAt,
                        expanding);
                if (held == null) {
                    yield null;
                }
                List<ObservedValue> made = new ArrayList<>();
                made.add(new ObservedValue.Absent());
                made.addAll(held);
                yield made;
            }
            case Shape.Sequence _, Shape.Mapping _, Shape.Unresolved _, Shape.Cases _,
                 Shape.Tuple _, Shape.Function _, Shape.Uninhabited _, Shape.Bottom _,
                 Shape.Erroneous _, Shape.Undecided _ -> null;
        };
        if (bare == null) {
            return null;
        }
        // The names the type wears, the outermost around the rest.
        List<ObservedValue> out = new ArrayList<>();
        for (ObservedValue each : bare) {
            ObservedValue worn = each;
            List<TypeSymbol> names = view.wrappers();
            for (int name = names.size() - 1; name >= 0; name--) {
                worn = new ObservedValue.Constructed(names.get(name), Map.of("value", worn));
            }
            out.add(worn);
        }
        return out;
    }

    /** Up to {@code most} records of {@code product}: every field at each of its values, the
     *  first field changing slowest. */
    private static List<ObservedValue> recordsOf(Shape.Product product, TermPath at,
                                                 RuleReadingSource source, int most,
                                                 Function<TermPath, List<ObservedValue>> numbersAt,
                                                 Set<TypeSymbol> expanding) {
        List<Map<String, ObservedValue>> made = new ArrayList<>();
        made.add(new LinkedHashMap<>());
        for (Map.Entry<String, Type> field : product.fields().entrySet()) {
            List<ObservedValue> values = valuesOf(field.getValue(), at.then(field.getKey()),
                    source, most, numbersAt, expanding);
            if (values == null) {
                return null;
            }
            List<Map<String, ObservedValue>> wider = new ArrayList<>();
            for (Map<String, ObservedValue> before : made) {
                for (ObservedValue each : values) {
                    if (wider.size() == most) {
                        break;
                    }
                    Map<String, ObservedValue> with = new LinkedHashMap<>(before);
                    with.put(field.getKey(), each);
                    wider.add(with);
                }
            }
            made = wider;
        }
        List<ObservedValue> out = new ArrayList<>();
        for (Map<String, ObservedValue> fields : made) {
            out.add(new ObservedValue.Constructed(product.name(), fields));
        }
        return out;
    }
}
