package souther.compiler.check;

import souther.compiler.observe.FieldTypes;
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
 * <p><b>Which names, and not what they hold.</b> Which declarations make a name readable is nominal
 * and is answered here. What one of those declarations holds under that name is
 * {@link FieldTypes}', asked of the world the reading is being made in — {@link #in} is that step,
 * and it is how a reader of an accepted program reads a surface without deriving a second answer to
 * what a field holds. {@link #declaredFields} is the same surface with the types the declarations
 * were read with, which is what a reader in that world already has.
 *
 * <p><b>Not what a value here is built out of.</b> {@link ConstructionDescent} answers that, and the
 * two answers are the same map at a record and are not the same question: a value of a sum is a
 * value of one of its cases, and a product of the shared fields is a value of none of them. Read
 * from there, a plan would compose a sum out of the part its cases have in common; read from here,
 * a walk deciding where to <em>write</em> a value would go somewhere no row writes anything. The
 * coincidence at a record is a law over the two answers and is not a reason for either to be the
 * other's implementation.
 *
 * <p><b>And this is what a walk over a value already written asks.</b> Reading is what such a walk
 * does: the case is settled in the value it holds, so what it may take is what every value of the
 * position carries, and a name only some case declares is not readable however many rows turn out
 * to be that case. The written relation answers nothing at a sum's shared name, so a walk that took
 * it read no value at every name a model reads through a sum.
 *
 * <p><b>Asked of a {@link Shape} and not of a {@link Type}.</b> A shape has had the names a value
 * wears taken off already, and whether they come off is a rule about what a {@code .} may name
 * rather than a policy each reader settles — {@link FieldRead} holds it, and is what a reader with
 * a type in hand asks. Started here, a shape would be read for a position whose names nobody had
 * decided about.
 *
 * @param declaredBy     the declarations the names are written on, outermost spread first. What a
 *                       rule over one of these fields is written on, which is not the same as what a
 *                       value standing here is written as: a sum's shared names are declared by the
 *                       data its cases spread, and a value there is written as one of the cases
 * @param declaredFields what is readable, with what the declarations this was read from say each
 *                       name holds, in the order those declarations write it — which is the order it
 *                       is walked and reported in
 */
public record ReadableFields(List<TypeSymbol> declaredBy, Map<String, Type> declaredFields) {

    public ReadableFields {
        declaredBy = List.copyOf(declaredBy);
        declaredFields = Collections.unmodifiableMap(new LinkedHashMap<>(declaredFields));
    }

    /**
     * What is readable off a value of this shape.
     *
     * <p>Exhaustive over {@link Shape}, with no {@code default}. A shape admitted later is answered
     * for here or stops this compiling, rather than arriving as a position whose names each reader
     * works out again.
     */
    public static ReadableFields of(Shape shape) {
        Readable here = readableOn(shape);
        return new ReadableFields(here.declaredBy(), here.fields());
    }

    /**
     * What {@code name} is declared to be where it is readable off a value of this shape, or null
     * where nothing of that name is.
     *
     * <p>The same question as {@link #of} asked about one name, for a reader that has one in hand
     * and no use for the rest — a walk taking a step of a path is asking whether it may take this
     * one. Answered off the same map rather than beside it, so there is no second rule about which
     * names are readable and no answer here that {@link #of} does not also give.
     *
     * <p>Here rather than at the caller because the map {@link #of} hands back is a copy: what a
     * reader after one name would otherwise do is have every name at the position copied out to
     * index one of them, once per step of every path walked over every row.
     */
    public static Type at(Shape shape, String name) {
        return readableOn(shape).fields().get(name);
    }

    /** What is readable, as the declarations hold it. Beside {@link ReadableFields} and not one:
     *  the maps here are the declarations' own, which is what lets a reader after one name index
     *  one without every name at the position being copied out first. */
    private record Readable(List<TypeSymbol> declaredBy, Map<String, Type> fields) {}

    private static final Readable NOTHING = new Readable(List.of(), Map.of());

    /**
     * What is readable off a value of this shape, and what declares it.
     *
     * <p>Exhaustive over {@link Shape}, with no {@code default}. A shape admitted later is answered
     * for here or stops this compiling, rather than arriving as a position whose names each reader
     * works out again.
     *
     * <p>One switch and not one per projection. Which names are readable and what they are written
     * on are answered together because they are one reading of the shape — asked apart, a shape
     * admitted later could have names here and nothing declaring them there, and what a rule over
     * one of those fields is written on would be missing with nothing refusing it.
     */
    private static Readable readableOn(Shape shape) {
        return switch (shape) {
            case Shape.Product product -> new Readable(List.of(product.name()), product.fields());
            // Read without opening a case, so what a value here carries whichever case it turned
            // out to be — and nothing where the cases share no spread. A field two cases happen to
            // declare alike is not shared: the sharing is nominal, and what is written on the sum
            // is what was written once and spread.
            case Shape.Sum sum -> switch (sum.common()) {
                case Shape.CommonProduct.Shared shared ->
                        new Readable(shared.origins(), shared.fields());
                case Shape.CommonProduct.None _ -> NOTHING;
            };
            // A newtype's contents are read where the names are taken off, which is TypeView's; what
            // a container holds is reached by holding it and not by naming it; and the rest carry no
            // names at all. None of them is a field access anybody may write here.
            case Shape.Scalar _, Shape.Unit _, Shape.Sequence _, Shape.Mapping _, Shape.Optional _,
                 Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ ->
                    NOTHING;
        };
    }

    /**
     * The same surface, with what each name holds answered by {@code world}.
     *
     * <p><b>The names are this reading's and the types are the world's.</b> Which names a value here
     * makes readable is nominal — a record's own fields, what every case of a sum spreads — and a
     * world says what a declaration holds under a name, never which names there are. Asked for the
     * whole of a declaration and merged, a world could widen the surface with a name nothing here
     * makes readable or narrow it by leaving one out, and a reader going through the one owner of
     * this question would still be reading a surface the world had decided.
     *
     * <p>A name this reading has and the world says nothing about is not readable in that world.
     * That is the state a text still being typed is in — a field written at a type that does not
     * resolve yet is a field its world says nothing about — and it does not arise in an accepted
     * program, whose world answers for every name its declarations write.
     *
     * <p>In the order this reading holds the names, which is the order the declarations write them:
     * the order a value is laid out in, and the order this is walked and reported in.
     */
    public Map<String, Type> in(FieldTypes world) {
        Map<String, Type> out = new LinkedHashMap<>();
        for (String name : declaredFields.keySet()) {
            Type held = heldIn(declaredBy, name, world);
            if (held != null) {
                out.put(name, held);
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /**
     * What {@code name} holds where it is readable off a value of this shape in {@code world}, or
     * null where nothing of that name is readable there.
     *
     * <p>{@link #in} asked about one name, and here for the reason {@link #at} is: a reader with one
     * name in hand would otherwise have every name at the position asked of the world and copied out
     * to index one of them.
     *
     * <p>Whether the name is readable at all is settled here before the world is asked, so the two
     * widths admit the same names — and neither lets a world make a name readable that this reading
     * does not.
     */
    public static Type at(Shape shape, String name, FieldTypes world) {
        Readable here = readableOn(shape);
        return here.fields().containsKey(name) ? heldIn(here.declaredBy(), name, world) : null;
    }

    /**
     * What {@code declaredBy} holds under {@code name} in {@code world}, or null where none of them
     * says.
     *
     * <p>The one rule both widths use, so a name is looked up the same way whether it was asked for
     * on its own or with every other. Asked in the order the declarations are held and the last that
     * answers wins: at most one of them writes a given name in a program that was accepted — a name
     * two of a sum's shared spreads both declared is refused where the spread is checked — so the
     * order settles nothing today, and it is followed rather than relied on being idle.
     */
    private static Type heldIn(List<TypeSymbol> declaredBy, String name, FieldTypes world) {
        Type held = null;
        for (TypeSymbol declaration : declaredBy) {
            Type there = world.of(declaration).get(name);
            if (there != null) {
                held = there;
            }
        }
        return held;
    }
}
