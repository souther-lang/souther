package souther.compiler.inputs;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.Type;

/**
 * Which number of a behavior's input an expression names, or nothing where it names none.
 *
 * <p>The companion of {@link InputPath}, one question further in. That answers which location an
 * expression points at; this answers which number a rule about it is written on, which is the
 * location's own content or something taken of it — and the two are not the same answer, because a
 * position holding a string is a position holding no number while every rule about its length is
 * about one.
 *
 * <p>One answer, for every reader that has to say which number a comparison is about. The reading
 * that draws lines and the reading that names what a run was steered by both ask it, and each
 * working it out for itself is two accounts of one number: matched afterwards by how a path is
 * spelled, two numbers taken of one location are one, which is the whole of what a line drawn on
 * the second of them is lost to.
 *
 * <p>Which of the standard library's calls take a number of a location is asked of
 * {@link NumericMeasures} rather than decided here, and asked of the operation the call resolved to
 * rather than of its spelling.
 */
public final class InputNumber {

    private InputNumber() {
    }

    /**
     * The number {@code e} names.
     *
     * <p>The argument of a taking has to be a location: {@code List.length(List.map(f, xs))} counts
     * something no path names, and a boundary on it could not be looked for in a row.
     */
    public static NumericTerm of(Core e, InputReads reads, Symbols symbols) {
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e);
        if (measured != null) {
            TermPath of = reads.pathOf(measured.of(), symbols);
            if (of != null) {
                return NumericTerm.TakenOf.of(measured.operation(), of,
                        reads.read().typeAt(of, symbols), symbols);
            }
            // A location the operation is not taken of, or a value standing at none. The second is
            // a walk's answer, and a number over the values it walked is a term of its own where
            // those values are read from a place.
            return overARun(measured, reads, symbols);
        }
        TermPath path = reads.pathOf(e, symbols);
        return path == null ? null : new NumericTerm.ValueOf(path);
    }

    /**
     * The number {@code measured} takes over the values a walk was given, or null where those
     * values are not read from a place.
     *
     * <p>Three answers have to be in hand, and each is somebody else's. That the walk answers one
     * value per element of what it was given is a fact about the operation that handed the closure
     * its elements, proved before the tree was rewritten. Where in an element the answer stands is
     * what the closure came to, read once and kept as the way there. And which position the
     * elements are at is the reading of the input's, as it is for every other term.
     *
     * <p>What the walk itself supplies is the element's binding and nothing more. The form it has
     * now is what a rewrite left, so it is asked for an identity and not for a meaning: reading the
     * answer off the shape would make the walks a rule can be written over a consequence of which
     * ones that rewrite happens to recognise, and a walk an author wrote by hand would be read as
     * a {@code map}.
     *
     * <p>The walk is met under whatever name is in scope, and what a name stands for is asked of
     * the reading that owns the question ({@link InputReads#meaningOf}) rather than read off the
     * tree. A model of any size binds the mapped list before totalling it, and a route that walked
     * only the expression as written would answer one thing for
     * {@code List.sum(List.map(f, xs))} and another for the same rule with a name in the middle —
     * which is a `let` changing what a model means. The environment the value was given in comes
     * with it, so what is read of the walk afterwards is read where the walk stands.
     *
     * <p>Null wherever any of the three is missing, which is a rule this compiler did not read
     * rather than a rule the model does not state — and is reported as one.
     */
    private static NumericTerm overARun(NumericMeasures.Measured measured, InputReads reads,
                                        Symbols symbols) {
        Core walk = measured.of();
        InputReads where = reads;
        // By the bindings met, so a name that came round to itself stops rather than being followed
        // again. Bindings are added on the way down and each tells itself from every other, so this
        // is the shape of the tree saying so and not a depth somebody chose.
        java.util.Set<souther.compiler.types.BindingId> met = new java.util.HashSet<>();
        while (walk instanceof Core.Read read) {
            if (!met.add(read.binding())
                    || !(where.meaningOf(read, symbols) instanceof ReadMeaning.Through through)) {
                return null;
            }
            walk = through.value();
            where = through.at();
        }
        souther.compiler.types.BindingId element =
                souther.compiler.core.GrowingFold.elementBindingOf(walk);
        if (element == null) {
            return null;
        }
        ElementProjection answered = where.elements().projectionAt(element);
        TermPath at = where.elementAt(element, symbols);
        if (answered == null || at == null) {
            return null;
        }
        TermPath under = answered.from(at);
        Type stands = where.read().typeAt(under, symbols);
        return stands == null ? null
                : NumericTerm.TakenOver.of(measured.operation(),
                        new RunSource.ProjectedOccurrences(under), stands, symbols);
    }

    /** The number a comparison is about, from whichever side names one. */
    public static NumericTerm compared(Core.Binary comparison, InputReads reads, Symbols symbols) {
        NumericTerm left = of(comparison.left(), reads, symbols);
        return left != null ? left : of(comparison.right(), reads, symbols);
    }
}
