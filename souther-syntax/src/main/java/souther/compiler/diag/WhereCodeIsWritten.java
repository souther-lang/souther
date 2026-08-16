package souther.compiler.diag;

import java.util.Objects;

/**
 * What a report says about where the code it is about is written.
 *
 * <p>Three answers, and two of them were one for a while. A report pointing at a file the reader
 * holds says the code is <em>here</em>; a report pointing at nothing says <em>nothing</em>. Both came
 * back as a null provenance, so a caller moving a report to somewhere a reader can be sent could hand
 * the first a module and be believed — and a caret moving is not the code moving.
 *
 * <p>Which is the mistake this whole change is about, made once more by the value that was written to
 * stop it. The rule is on {@link QuotedFrom} and on {@link DiagnosticPlace.Unavailable} and on
 * {@link Citation#writtenAtFields}, each in its own words: a negative answer is an answer, and an
 * absence that carries two of them is where a reader starts guessing.
 *
 * <p>So the negative side is two named states. {@link Here} is a report that has already answered;
 * {@link Unstated} is one that has not, and is the only one a caller may answer for.
 */
public sealed interface WhereCodeIsWritten {

    /** The code is written where the report points, in something the reader is looking at. */
    record Here() implements WhereCodeIsWritten {

        static final Here IT = new Here();
    }

    /** The code is written in {@code module}, which is not where the report points. */
    record Elsewhere(SourceProvenance module) implements WhereCodeIsWritten {

        public Elsewhere {
            Objects.requireNonNull(module, "code written elsewhere was written somewhere");
        }
    }

    /**
     * The report says nothing about where its code is written.
     *
     * <p>Not "here", and not "elsewhere and I forgot": a report that points at nothing has no
     * position to have said it through and did not say it any other way. The only state a caller may
     * answer for, because it is the only one with nothing to contradict.
     */
    record Unstated() implements WhereCodeIsWritten {

        static final Unstated IT = new Unstated();
    }
}
