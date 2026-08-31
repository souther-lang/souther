package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What can be read off a value standing at a position, without narrowing it to anything.
 *
 * <p>The names a field access may write there, and the declarations they are written on. A record's
 * are its own fields; a sum's are the fields of the declarations every one of its cases spreads,
 * which are readable at every value of the sum because every value of it carries them.
 *
 * <p><b>Not what a value here is built out of.</b> {@link ConstructionDescent} answers that, and the
 * two answers are the same map at a record and are not the same question: a value of a sum is a
 * value of one of its cases, and a product of the shared fields is a value of none of them. Read
 * from there, a plan would compose a sum out of the part its cases have in common; read from here,
 * a walk into what a row wrote would go somewhere no row writes anything. The coincidence at a
 * record is a law over the two answers and is not a reason for either to be the other's
 * implementation.
 *
 * <p><b>Asked of a {@link Shape} and not of a {@link Type}.</b> How far to look through the names a
 * value wears is the reader's own policy — the elaboration of a field read looks through none of
 * them, and a walk over a behavior's positions looks through all of them — and {@link TypeView}
 * holds both directions for that reason. Started here, that policy would be decided for every
 * reader by whichever one asked first.
 *
 * @param declaredBy the declarations the names are written on, outermost spread first. What a rule
 *                   over one of these fields is written on, which is not the same as what a value
 *                   standing here is written as: a sum's shared names are declared by the data its
 *                   cases spread, and a value there is written as one of the cases
 * @param fields     what is readable, in the order the declarations write it — which is the order
 *                   it is walked and reported in
 */
public record ReadableFields(List<TypeSymbol> declaredBy, Map<String, Type> fields) {

    /** Nothing is readable off a value here without narrowing it first. */
    private static final ReadableFields NONE = new ReadableFields(List.of(), Map.of());

    public ReadableFields {
        declaredBy = List.copyOf(declaredBy);
        fields = Collections.unmodifiableMap(new LinkedHashMap<>(fields));
    }

    /**
     * What is readable off a value of this shape.
     *
     * <p>Exhaustive over {@link Shape}, with no {@code default}. A shape admitted later is answered
     * for here or stops this compiling, rather than arriving as a position whose names each reader
     * works out again.
     */
    public static ReadableFields of(Shape shape) {
        return switch (shape) {
            case Shape.Product product -> new ReadableFields(List.of(product.name()),
                    product.fields());
            // Read without opening a case, so what a value here carries whichever case it turned
            // out to be — and nothing where the cases share no spread. A field two cases happen to
            // declare alike is not shared: the sharing is nominal, and what is written on the sum
            // is what was written once and spread.
            case Shape.Sum sum -> switch (sum.common()) {
                case Shape.CommonProduct.Shared shared ->
                        new ReadableFields(shared.origins(), shared.fields());
                case Shape.CommonProduct.None _ -> NONE;
            };
            // A newtype's contents are read where the names are taken off, which is TypeView's; what
            // a container holds is reached by holding it and not by naming it; and the rest carry no
            // names at all. None of them is a field access anybody may write here.
            case Shape.Scalar _, Shape.Unit _, Shape.Sequence _, Shape.Mapping _, Shape.Optional _,
                 Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ -> NONE;
        };
    }
}
