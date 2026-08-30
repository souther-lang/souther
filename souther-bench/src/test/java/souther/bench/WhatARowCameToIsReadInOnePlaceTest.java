package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a row came to is turned into a measure's loss once, and the readings of the rows are asked
 * for rather than gathered.
 *
 * <p>Two vocabularies meet here. What stopped a row is a fact about the row, written where the row
 * stopped; what a measure can no longer answer is a fact about the measure. Joined in more than one
 * place they can differ, and they did: a measure walked the dispositions itself and produced a
 * weakening of its own, one that named the row without saying which source it is in — so two rows of
 * one behavior were one fact (issue #996).
 *
 * <p>The same shape one level up. Which rows a behavior has and what stopped them being seen is one
 * reading, and the document walked the sources to build a second — so what a report counted and what
 * its measures were counted over were two answers that happened to agree.
 *
 * <p>Read off the bytecode rather than the sources: what reaches a type is four things and not one
 * ({@link Compiled}), and a javadoc naming a class is not a use of it.
 */
class WhatARowCameToIsReadInOnePlaceTest {

    private static final String DISPOSITION = "souther.compiler.observe.Disposition";

    /** Where a row's outcome becomes a reason a measure could not read everything. */
    private static final String PRODUCER = "souther.compiler.examples.ExampleVerifier";

    /**
     * Nothing but the producer asks whether a row did not come back.
     *
     * <p>Every other reader takes the reason, which says which row and which source as well as what
     * stopped it. Asking the disposition again is asking a question this one has already answered,
     * in words that carry less.
     *
     * <p>{@code PENDING} is not this. Whether a row is waiting for a {@code let} is a fact about
     * what is written rather than about a run that fell short, so it is counted where it is shown;
     * what this is about is a row that was run and left undecided.
     */
    @Test
    void nothingButTheProducerReadsThatARowDidNotComeBack() throws IOException {
        Set<String> asking = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            // The enum's own class holds it too, in the members a compiler writes for every enum.
            // Naming itself is not reading itself.
            if (site.owner().equals(DISPOSITION) && site.member().equals("INCOMPLETE")
                    && !site.from().startsWith(PRODUCER)
                    && !site.from().equals(DISPOSITION)) {
                asking.add(site.at());
            }
        }
        assertEquals(Set.of(), asking,
                "a reader asked a row whether it came back instead of reading the reason written"
                        + " where it stopped, which is a second statement of one fact");
    }

    /** And the producer does ask, so the check above saw something rather than nothing. */
    @Test
    void theProducerReadsIt() throws IOException {
        assertFalse(Compiled.sites().stream()
                        .noneMatch(site -> site.from().startsWith(PRODUCER)
                                && site.owner().equals(DISPOSITION)
                                && site.member().equals("INCOMPLETE")),
                "the one reader of a row's disposition is where a row stops");
    }

    /**
     * One method reads what a module's sources saw, and it is the one the answer is made in.
     *
     * <p>{@code Adequacy.rowsOf} makes the reading a measure is counted over. Its callers each
     * decided for themselves what to do where the build reads no rows — the same `level → nothing
     * was asked` reading, written five times — so what the answer says about a level and what a
     * measure made of it were two statements of one thing. The answer says it now, and the reading
     * is reached only through the answer (issue #996).
     *
     * <p>Of that method and not of every one named for the rows. What a behavior's rows are is asked
     * elsewhere, by whoever is not measuring, and a check spelled by a member's name alone answers
     * about whatever else was named that.
     */
    @Test
    void whatTheSourcesSawIsGatheredWhereTheAnswerIsMade() throws IOException {
        Set<String> gathering = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals("souther.compiler.query.Adequacy")
                    && site.member().equals("rowsOf")
                    && !site.at().startsWith("souther.compiler.query.Adequacy$Rows#compute")) {
                gathering.add(site.at());
            }
        }
        assertEquals(Set.of(), gathering,
                "a caller reached past `Adequacy.Rows` for the gathering under it, which is where"
                        + " what a level asked for stops being one answer");
    }

    /**
     * Nothing outside the query layer gathers the rows out of the sources.
     *
     * <p>{@code Output.Examples} is what one source's evaluation left. Which rows a behavior has is
     * an answer over all of them together, and it is one answer: a caller assembling it again
     * decides for itself what a source that did not answer means, and both callers that did read it
     * as a source holding no rows.
     */
    @Test
    void theReadingOfARowIsAskedForRatherThanGathered() throws IOException {
        Set<String> gathering = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            // The benchmarks drive the queries to time them, which is asking for the evaluation
            // rather than reading what it left for an answer of their own.
            if (site.owner().startsWith("souther.compiler.query.Output$Examples")
                    && !site.from().startsWith("souther.compiler.query.")
                    && !site.from().startsWith("souther.bench.")) {
                gathering.add(site.at());
            }
        }
        assertEquals(Set.of(), gathering,
                "a reader outside the queries assembled what a module's sources saw. What every"
                        + " behavior's rows came to is `Adequacy.Rows`, and a second assembly of it"
                        + " is a second answer to keep agreeing");
    }
}
