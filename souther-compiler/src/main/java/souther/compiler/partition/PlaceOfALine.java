package souther.compiler.partition;

import java.util.Objects;

/**
 * One place a line of a comparison's author was put: the line, and the relation over the
 * behavior's input it came to there.
 *
 * <p>Two questions with two owners. Which line it is is the author's, and the same in every copy
 * of a helper ({@link PartOfAComparison}); it is what a row is owed for. Where the line came to is
 * the reading's: a call hands the definition values the caller chose, and one line lands at one
 * relation for each case of them. Each of those is a reading of the one line, and they are told
 * apart here so that what is worked out for one — where it decides, how a row reaches it — is not
 * filed under another.
 *
 * @param line     which of the author's lines
 * @param relation the relation the line came to, as the reading spelled it: one spelling for one
 *                 relation
 */
public record PlaceOfALine(PartOfAComparison line, String relation) {

    public PlaceOfALine {
        Objects.requireNonNull(line, "a place is of some line");
        Objects.requireNonNull(relation, "and is some relation");
    }
}
