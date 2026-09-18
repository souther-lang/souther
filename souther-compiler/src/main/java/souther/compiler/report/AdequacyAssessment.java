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
 * <p>Of a scope, and every scope this report can be narrowed to has one. A narrowed report works
 * its own out again from the parts it kept rather than selecting from these, so the two are
 * related by what the narrowing keeps and not by containment: narrowed to a module it holds a
 * subset of these, and narrowed to a behavior it can hold an entry this does not — an obligation
 * of the module's declarations, answered again without the rows of the behaviors that left
 * ({@link AdequacyReport#only(String, String)}).
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
