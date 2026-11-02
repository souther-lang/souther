package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.meta.ModulePath;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Which lines a report numbers is an answer the store compares, so whoever reads it is run again
 * after an edit that moves the numbers and is left alone after one that does not.
 *
 * <p>Held for the module and not for any point, so what it asks is the module's: an edit to a
 * behavior with no line in common with the numbered ones leaves the value as it was, and an edit to
 * a numbered line does not. A reader is observed by counting how many times it ran.
 */
class WhatAReportNumbersIsAnAnswerOfItsOwnTest {

    private static final String SOURCE = """
            module m

            behavior clamp : (n: Int) -> Int

            let clamp (n) = if n > 50 then 50 else n

            behavior full : (n: Int) -> Bool

            let full (n) = clamp(n) == 50

            example full
                | (50) -> true
                | (49) -> false
                | (0) -> false
            """;

    private static final String WITH_ANOTHER_BEHAVIOR = SOURCE + """

            behavior shout : (s: Int) -> Int

            let shout (s) = s + 1
            """;

    private static final String WITH_ANOTHER_LINE = SOURCE.replace("n > 50", "n > 60");

    /** A reader of the numbers, which counts the times it ran. */
    private record Reader(AtomicInteger ran) implements Key<Boolean> {

        @Override
        public Answer<Boolean> compute(Db db) {
            ran.incrementAndGet();
            WhereTheReadingsDiffer apart = db.ask(new Adequacy.ToldApart("m",
                    Adequacy.linesAskedOf(db))).value();
            return Answer.of(!WhereTheReadingsDiffer.NONE.equals(apart));
        }
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY).writtenOn(TestDay.DATE);
        compilation.measure(Adequacy.Asked.fullReport());
        return compilation;
    }

    private static void edited(Compilation compilation, String source) {
        compilation.update(Map.of("a.sou", source), Set.of(), TestDay.DATE);
        compilation.measure(Adequacy.Asked.fullReport());
    }

    /** The value has numbers in it, so the two checks below are about something. */
    @Test
    void theModelUnderTestNumbersSomeLines() {
        AtomicInteger ran = new AtomicInteger();

        assertEquals(true, compiled().db().ask(new Reader(ran)).value());
    }

    /** A behavior that adds no line to the numbered ones comes to the value that was there, so the
     *  reader of it is not run again — though the points it was worked out from are not the ones
     *  it was. */
    @Test
    void anEditThatMovesNoNumberLeavesItsReaderAlone() {
        Compilation compilation = compiled();
        AtomicInteger ran = new AtomicInteger();
        Reader reader = new Reader(ran);
        compilation.db().ask(reader);
        WhereTheReadingsDiffer before = compilation.db().ask(new Adequacy.ToldApart("m",
                Adequacy.linesAskedOf(compilation.db()))).value();

        edited(compilation, WITH_ANOTHER_BEHAVIOR);
        compilation.db().ask(reader);
        WhereTheReadingsDiffer after = compilation.db().ask(new Adequacy.ToldApart("m",
                Adequacy.linesAskedOf(compilation.db()))).value();

        assertEquals(before, after);
        assertEquals(1, ran.get(), "the reader ran once, for the numbers that were there");
    }

    /** A numbered line that is edited is a different value, and its reader is run again. */
    @Test
    void anEditToANumberedLineRunsItsReaderAgain() {
        Compilation compilation = compiled();
        AtomicInteger ran = new AtomicInteger();
        Reader reader = new Reader(ran);
        compilation.db().ask(reader);
        WhereTheReadingsDiffer before = compilation.db().ask(new Adequacy.ToldApart("m",
                Adequacy.linesAskedOf(compilation.db()))).value();

        edited(compilation, WITH_ANOTHER_LINE);
        compilation.db().ask(reader);
        WhereTheReadingsDiffer after = compilation.db().ask(new Adequacy.ToldApart("m",
                Adequacy.linesAskedOf(compilation.db()))).value();

        assertNotEquals(before, after);
        assertEquals(2, ran.get(), "and again, for the numbers that came of the edit");
    }
}
