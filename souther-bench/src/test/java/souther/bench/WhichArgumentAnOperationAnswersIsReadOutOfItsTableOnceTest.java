package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The table saying which of its arguments an operation answers is read in one place, and its rows
 * are not passed on to anybody.
 *
 * <p>Two claims, because either alone leaves the drift the other stops. The library defines
 * {@code Int.min} by cases, and two readers want them: the recipe recorded for a value that is one
 * of several, and the reading of a clause as the cases of the operation standing in it. While each
 * read the table for itself, the second had them and the first did not, so the same value came out
 * bounded where a clause stood over it and unbounded where one did not (#974) — one table with two
 * readers, drifting, which is the shape #935 was.
 *
 * <p><b>The rows are not the arms.</b> Moving the lookup into one place and handing the row on would
 * leave the reading of it in two: a row names an argument of an operation, and turning that into a
 * value means knowing which position of which call it meant. So the table's own vocabulary stops at
 * {@code Choice}, which answers in the values the call was given, and nothing downstream can ask the
 * question a second way because nothing downstream is given anything to ask it about.
 *
 * <p>Read off the bytecode rather than the sources: what reaches a type is four things and not one
 * ({@link Compiled}), and a javadoc naming the table for the reader's sake is not a reading of it.
 */
class WhichArgumentAnOperationAnswersIsReadOutOfItsTableOnceTest {

    private static final String RULES = "souther.compiler.check.DischargeRules";

    /** The one class that reads the table, and the class the table is written in, whose own rows
     * reach each other however they are written. */
    private static final String READER = "souther.compiler.check.Choice";

    /** Where the cases are declared, and what holds them to the library. Both reach a row by
     * declaring one and by holding it to a signature, which is not handing it to a reader. */
    private static final String FACTS = "souther.compiler.semantics.OperationFact";

    /** The row types: one case of a definition, and one relation a case is reached under. Generic
     * in their word for an argument, so the one shape is the authored row and the bound one. */
    private static final Set<String> ROWS = Set.of("souther.compiler.semantics.DefinitionCase",
            "souther.compiler.semantics.ArgumentsStand");

    private static final Set<String> DECLARING = Set.of(FACTS,
            "souther.compiler.semantics.OperationFacts",
            "souther.compiler.check.OperationFactBinder",
            // A row reaches itself: its own equality and rendering read its parts.
            "souther.compiler.semantics.DefinitionCase",
            "souther.compiler.semantics.ArgumentsStand");

    @Test
    void nothingButTheChoiceItselfAsksWhatAnOperationChoosesBetween() throws IOException {
        Set<String> asking = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals(RULES) && site.member().equals("chosenBy")) {
                asking.add(site.from());
            }
        }
        assertEquals(Set.of(READER), asking,
                "the table is read where the arms of a choice are made, and nowhere else."
                        + " A second reader of it answers about the same call in its own words, and"
                        + " the two come apart the day the library changes which argument a case"
                        + " answers");
    }

    @Test
    void aRowOfTheTableIsNotHandedToAnybody() throws IOException {
        Set<String> reaching = new LinkedHashSet<>();
        boolean readAtAll = false;
        for (Compiled.Site site : Compiled.sites()) {
            if (!ROWS.contains(site.owner())) {
                continue;
            }
            readAtAll = true;
            if (!site.from().equals(READER) && !site.from().startsWith(RULES)
                    && DECLARING.stream().noneMatch(site.from()::startsWith)) {
                reaching.add(site.at());
            }
        }
        assertTrue(readAtAll, "no row of the table was reached at all, so this saw nothing rather"
                + " than seeing that nothing was wrong");
        assertEquals(Set.of(), reaching,
                "a row of the table reached outside the class that lowers it. What a row names is an"
                        + " argument of an operation, and reading that is the question the lowering"
                        + " exists to answer once — a reader handed the row asks it again");
    }
}
