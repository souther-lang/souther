package souther.compiler.query;

import souther.compiler.partition.Generator;

/**
 * What a generation came to at one point of one authored line.
 *
 * <p>One of these per point, however many readings the line has. A row at the line shows something
 * about the type, and one row anywhere shows it — so the work is one piece and the answer about it
 * is one answer. Composed per reading, one authored line is handed to an author as four things to
 * write.
 *
 * <p><b>The row's behavior is where it was composed and not who owes it.</b> Who owes it is whose
 * rules settled the point ({@link souther.compiler.partition.PointAttribution}) — the declaration
 * that drew the line, or the body that did. Where it was composed is a reading in whose terms the
 * row can be written, and which of them managed it is a fact about this run: another one may manage
 * it after an edit that did not touch the line. So it is carried as provenance, for the block the
 * row goes in, and nothing reads ownership off it.
 */
public sealed interface PointResolution {

    /**
     * A row stands at the line, written in one reading's terms.
     *
     * <p>The first reading the request walked that composed one, which is enough for the line: what
     * the two points against a line ask is the same at every reading of it — checked where a debt's
     * demands are — so a row standing at one reading's point stands at the line.
     *
     * <p>Which reading composed it is carried all the same, because not every reader is asking
     * about the line. A row is written in the terms of the position it was composed at, so a reader
     * asking what stands at one coordinate is asking whether that coordinate is this one — and told
     * only the behavior, two positions of one behavior come back indistinguishable and the row
     * written for one is offered as the answer at the other.
     */
    record Generated(BorderObligationPointAssessment.Reading at, Generator.GeneratedRow row)
            implements PointResolution {

        public Generated {
            if (at == null || row == null) {
                throw new IllegalArgumentException("a row was composed by walking some position's"
                        + " inputs, and this is neither");
            }
        }

        /** Which behavior's inputs were walked, which is where the row belongs. */
        public String composedBy() {
            return at.behavior();
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
    record Unresolved(SearchCoverage coverage) implements PointResolution {

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
    record NoSearch(Cause cause) implements PointResolution {

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
