package souther.compiler.inputs;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;

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
            // Null where the call names a location the operation is not taken of, which a guard can
            // write and the type checker has already refused elsewhere. Answered here as "no
            // number", which is what every reader of one is ready for.
            return of == null ? null : NumericTerm.TakenOf.of(measured.operation(), of,
                    reads.read().typeAt(of, symbols), symbols);
        }
        TermPath path = reads.pathOf(e, symbols);
        return path == null ? null : new NumericTerm.ValueOf(path);
    }

    /** The number a comparison is about, from whichever side names one. */
    public static NumericTerm compared(Core.Binary comparison, InputReads reads, Symbols symbols) {
        NumericTerm left = of(comparison.left(), reads, symbols);
        return left != null ? left : of(comparison.right(), reads, symbols);
    }
}
