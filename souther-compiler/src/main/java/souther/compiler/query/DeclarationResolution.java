package souther.compiler.query;

import souther.compiler.partition.Generator;

/**
 * What a generation came to at one point of one authored line.
 *
 * <p>One of these per point, however many readings the line has. A row at the line shows something
 * about the type, and one row anywhere shows it — so the work is one piece and the answer about it
 * is one answer (issue #1076). Composed per reading, the same authored line was handed to an author
 * as four things to write.
 *
 * <p><b>The row's behavior is where it was composed and not who owes it.</b> What owes the row is
 * the declaration that drew the line. A behavior carrying the type is a reading in whose terms the
 * row can be written, and which of them managed it is a fact about this run: another one may manage
 * it after an edit that did not touch the line. So it is carried as provenance, for the block the
 * row goes in, and nothing reads ownership off it.
 */
public sealed interface DeclarationResolution {

    /**
     * A row stands at the line, written in one reading's terms.
     *
     * <p>The first reading the request walked that composed one, which is enough: what the two
     * points against a line ask is the same at every reading of it — checked where a debt's demands
     * are — so a row standing at one reading's point stands at the line. Which reading it came from
     * is not part of the answer to whether the line can be written.
     */
    record Generated(String composedBy, Generator.GeneratedRow row) implements DeclarationResolution {

        public Generated {
            if (composedBy == null || row == null) {
                throw new IllegalArgumentException("a row was composed by walking some behavior's"
                        + " inputs, and this is neither");
            }
        }
    }

    /**
     * Every reading the request walked, and none of them composed a row.
     *
     * <p>What each of them came to is in the coverage and is not summarised here. The readings fail
     * for different reasons — one whose rules leave no value at the point, one whose candidates were
     * all refused, one the search stopped short of — and a single reason carried in this arm would
     * be one of them standing for the rest, chosen by the order the walk happened to take. What the
     * line itself settles, if anything, is {@link SearchCoverage#provesTheLineCannotBeWritten}.
     */
    record Unresolved(SearchCoverage coverage) implements DeclarationResolution {

        public Unresolved {
            if (coverage == null) {
                throw new IllegalArgumentException("a walk that came back came back with a walk");
            }
        }
    }

    /**
     * No search was made, and the point is not one this asks for a row at.
     *
     * <p>Apart from a search that found nothing, and the difference is not a matter of degree: those
     * readings were looked at and this point was not, because looking would tell nobody anything.
     */
    record NoSearch(Cause cause) implements DeclarationResolution {

        public NoSearch {
            if (cause == null) {
                throw new IllegalArgumentException("nothing was searched for some reason");
            }
        }
    }

    /**
     * Why a point is not one a row is looked for at.
     *
     * <p>The two are opposite states and are told apart for that reason. One is work that is done;
     * the other is not knowing whether there is work. Written as one, an author would be told the
     * same thing about a line their rows already stand at and about a line nothing measured.
     */
    enum Cause {

        /** A row this compilation read already stands at the line. There is nothing to compose. */
        A_ROW_ALREADY_STANDS,

        /** Nothing measured the point, so there is no shortfall here to answer — and a row composed
         *  for one would answer a question that was never asked. */
        NOTHING_MEASURED
    }
}
