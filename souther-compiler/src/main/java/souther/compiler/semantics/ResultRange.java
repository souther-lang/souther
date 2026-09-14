package souther.compiler.semantics;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;

/**
 * Where an operation's result runs, as far as a range of one number carries it.
 *
 * <p><b>A projection and not a translation.</b> What an operation declares of its result is a list
 * of rows relating that result to the arguments and to constants, under conditions on the arguments;
 * a range holds two ends and nothing else. So a row this cannot put on an end is left out, and what
 * comes back is where the result is known to run and not everything that is known about it. A reader
 * wanting the relations reads the rows — that is what the discharge does, which is why a row
 * bounding {@code Int.floorMod(x, k)} by {@code k} is not lost by anyone: it is lost here, where a
 * range has no name for {@code k}, and read there, where it has.
 *
 * <p>Leaving a row out is always the wider answer. Every row narrows, so a range that dropped one
 * holds every value the whole list holds and possibly more — this can be read where a fact was never
 * discharged, and never the other way about.
 *
 * <p>Which rows come out therefore depends on what the reader can say about the arguments, and that
 * is the parameter. A reader holding a call answers them all; one holding only the operation answers
 * {@link ConstantArguments#none()} and gets the rows that name nothing, which for an operation the
 * language gives no number is every row it has ({@code check.OperationFactBinder} holds a bound to
 * naming only an argument that is a number, which is what makes that so).
 *
 * <p><b>Handed the rows, and looking nothing up.</b> Whose rows they are, and whether they have
 * been held to the library, is the caller's to know; what this does is read the ones it is given.
 * Given a name and left to find the rows itself, this would be a second place the rows are looked
 * for, and the one place a reader could reach them without whatever holds them having run.
 */
public final class ResultRange {

    /**
     * Where a result runs, under what {@code arguments} can say, given the {@code rows} declared of
     * it.
     *
     * <p>Every end, so two rows about one side leave the tighter of them: the rows are one statement
     * about one number, and reading them one at a time would answer with whichever was written
     * last.
     */
    public static <A> NumericDomain.Bounds of(List<ResultBound<A>> rows,
                                              ConstantArguments<A> arguments) {
        NumericDomain.Bounds runs = NumericDomain.Bounds.OPEN;
        for (ResultBound<A> row : rows) {
            if (!arguments.satisfy(row.provided())) {
                continue;
            }
            NumericDomain.Bounds one = endOf(row, arguments);
            if (one != null) {
                runs = runs.meet(one);
            }
        }
        return runs;
    }

    /** The end one row puts on the result, or null where this reader cannot say where that end
     *  stands. */
    private static <A> NumericDomain.Bounds endOf(ResultBound<A> row,
                                                  ConstantArguments<A> arguments) {
        Count at = standsAt(row, arguments);
        if (at == null) {
            return null;
        }
        // No default and no `NE`: a bound is where a result stops, and `ResultBound` refuses the one
        // relation that is not an end. A relation added to the domain is a case here rather than a
        // row that quietly puts no end anywhere.
        return switch (row.rel()) {
            case GE -> new NumericDomain.Bounds(Endpoint.inclusive(at), null);
            case GT -> new NumericDomain.Bounds(Endpoint.exclusive(at), null);
            case LE -> new NumericDomain.Bounds(null, Endpoint.inclusive(at));
            case LT -> new NumericDomain.Bounds(null, Endpoint.exclusive(at));
            case EQ -> new NumericDomain.Bounds(Endpoint.inclusive(at), Endpoint.inclusive(at));
            case NE -> throw new IllegalStateException(
                    "a bound cannot be written with `NE`, and one was: " + row);
        };
    }

    /** The count the row's end is at, or null where the argument it is against says nothing here. */
    private static <A> Count standsAt(ResultBound<A> row, ConstantArguments<A> arguments) {
        if (row.against() == null) {
            return Count.of(row.offset());
        }
        Optional<BigDecimal> against = arguments.at(row.against());
        return against.map(value -> Count.of(value.add(row.offset()))).orElse(null);
    }

    private ResultRange() {}
}
