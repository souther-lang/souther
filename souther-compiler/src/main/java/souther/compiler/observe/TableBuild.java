package souther.compiler.observe;

import souther.compiler.diag.Diagnostic;

import java.util.List;

/**
 * Whether the tables a source's {@code fake} rows state were built here, and what is wrong with them
 * if they were.
 *
 * <p>Two, for the reason {@link RowRun} has two, and this is where the want of them was doing
 * damage: a build that did not happen answered with the empty list a build that found nothing wrong
 * answers with. A module whose classes could not be made had its fakes reported as sound.
 */
public sealed interface TableBuild {

    /** The tables were built, and this is what building them said about them. */
    record Built(List<Diagnostic> wrong) implements TableBuild {

        public Built {
            wrong = List.copyOf(wrong);
        }
    }

    /** Nothing was built, so nothing is known about them from here. */
    record NotBuiltHere() implements TableBuild {}
}
