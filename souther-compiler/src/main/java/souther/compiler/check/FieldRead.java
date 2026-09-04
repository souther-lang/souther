package souther.compiler.check;

import souther.compiler.observe.FieldTypes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

/**
 * What a {@code .} written on a value standing at a position may name.
 *
 * <p>The one reading of a field access, and the only place a type is crossed at a {@code .}. What is
 * readable off a value is not what a value of a declaration is laid out as: a sum is laid out as
 * nothing — a value of it is a value of one of its cases — while a name every one of its cases
 * spreads is readable on every value of it. Asked of the layout, a reader is told a shared name is a
 * field nothing declares; asked here, it is told what the language reads there.
 *
 * <p><b>The nominal barrier is here.</b> A name worn over a value is not looked through: a
 * {@code data AmountN = Int} reads its own {@code value} and nothing of the {@code Int}, and a
 * {@code data StageN = Stage} reads no case's field of the sum it names. That is what a {@code .}
 * means and not a policy of whoever is reading — an elaboration, a walk that types what a text
 * wrote, and an editor asking what may follow a {@code .} are one answer, so a reader adding a
 * second decision about the names would be answering a question this has already answered.
 *
 * <p><b>Which world, from the caller.</b> Which names are readable is nominal and comes from the
 * declarations ({@link ReadableFields}); what one of them holds is {@code world}'s. An accepted
 * program's fields are what its check settled and a text that has not checked has what its
 * declarations resolve to so far, and neither reader may fall back to the other's answer.
 *
 * @param symbols what the names in a position denote
 * @param world   what a declaration holds under each of its names, in the world this reading is
 *                being made in
 */
public record FieldRead(Symbols symbols, FieldTypes world) {

    public FieldRead {
        if (symbols == null || world == null) {
            throw new IllegalArgumentException(
                    "a field read is made against declarations and a world that says what they hold");
        }
    }

    /**
     * Every name a {@code .} on a value of {@code position} may write, with what it holds.
     *
     * <p>The surface and not one lookup, because the surface is the question: an editor listing what
     * may follow a {@code .} and an elaboration typing the one name that was written read the same
     * answer, and a second producer of it is how the two came to disagree.
     *
     * <p>Empty where nothing is readable without opening a case first — which is an answer about the
     * position and not a failure to read it.
     */
    public Map<String, Type> at(Type position) {
        return switch (surfaceOf(position)) {
            case Surface.OfAName(TypeSymbol worn) -> world.of(worn);
            case Surface.OfAShape(Shape shape) -> ReadableFields.of(shape).in(world);
        };
    }

    /**
     * What {@code field} holds on a value of {@code position}, or null where nothing readable there
     * is written under that name.
     *
     * <p>The same question as {@link #at} asked about one name, and answered without every name at
     * the position being asked of the world and copied out to index one of them. Off the same
     * reading of the position, so there is no second rule here about how far the names a value wears
     * come off and no name answered here that {@link #at} does not also give.
     */
    public Type of(Type position, String field) {
        return switch (surfaceOf(position)) {
            case Surface.OfAName(TypeSymbol worn) -> world.of(worn).get(field);
            case Surface.OfAShape(Shape shape) -> ReadableFields.at(shape, field, world);
        };
    }

    /** What a {@code .} on a value here reads: the one declaration a worn name is, or the shape a
     *  value under no name has. */
    private sealed interface Surface {

        /** A name the value is written under. Its own declaration and no further — the single field
         *  a newtype is written with (spec §newtype), and nothing of what that field holds. */
        record OfAName(TypeSymbol worn) implements Surface {}

        /** A value under no name of its own: what the shape makes readable. */
        record OfAShape(Shape shape) implements Surface {}
    }

    /**
     * Which of the two {@code position} is.
     *
     * <p>Beside the two entries and in neither, so the names a value wears come off in one place
     * however wide the question being asked is. Decided in each, the surface a reader lists and the
     * name it looks up could stop being the same reading.
     */
    private Surface surfaceOf(Type position) {
        TypeView view = TypeView.of(position, symbols);
        return view.isWrapped() ? new Surface.OfAName(view.wrappers().getFirst())
                : new Surface.OfAShape(view.shape());
    }
}
