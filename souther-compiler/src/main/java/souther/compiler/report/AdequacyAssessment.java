package souther.compiler.report;

import souther.compiler.query.Adequacy;

import java.util.List;

/**
 * What the measures of one scope came to, before anything is ranked.
 *
 * <p>Two lists and no verdict. A gap is a measure that was made and found something a row is owed
 * at; an uncertainty is a thing that has not come to an answer. Which of them settles the word a
 * reader is shown is {@link AdequacyReport#adequacy()}'s, and that ranking is where one of these
 * stops being visible — a scope with a gap is refused whatever else went unanswered, and the
 * uncertainties under it are no less real for being outranked.
 *
 * <p><b>Held apart from the verdict because a reader is sent somewhere by an uncertainty and not
 * by the verdict.</b> {@link ReaderDisposition} is a function of one of these entries, and a
 * question about where the entries lead is a question about this list. Asked of what keeps a
 * verdict open instead, the same question is answered over whichever scopes happen to have no gap,
 * and an entry sitting beside a gap is read as an entry that does not exist.
 *
 * <p>Of a scope, and every scope this report can be narrowed to has one. What a narrowed report
 * holds is the entries whose subject it kept, so narrowing selects from these rather than working
 * them out again ({@link AdequacyReport#only(String, String)}).
 *
 * @param gaps what the measures found that the rows are asked for and is not there
 * @param uncertainties what has not come to an answer, whatever the verdict makes of them
 */
public record AdequacyAssessment(List<Adequacy.Finding> gaps,
                                 List<AdequacyUncertainty> uncertainties) {

    public AdequacyAssessment {
        gaps = List.copyOf(gaps);
        uncertainties = List.copyOf(uncertainties);
    }
}
