package souther.compiler.report;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The evidence a gate shows for the two texts it compared. It reads only the two texts and the
 * labels they are shown under; nothing about how either was produced reaches here.
 */
class UnifiedDiffTest {

    @Test
    void aChangedLineIsShownAgainstItsContext() {
        String from = "a\nb\nc\n";
        String to = "a\nB\nc\n";

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from, to);

        assertEquals("""
                --- m.sou
                +++ m.sou (formatted)
                @@ -1,3 +1,3 @@
                 a
                -b
                +B
                 c
                """, diff);
    }

    @Test
    void twoTextsThatAreTheSameHaveNothingToShow() {
        assertEquals("", UnifiedDiff.of("m.sou", "m.sou (formatted)", "a\nb\n", "a\nb\n"));
    }

    /**
     * Changes further apart than twice the context are separate hunks. Written as one they would
     * carry every line between them, which for a file formatted in two places is the whole file.
     */
    @Test
    void changesTooFarApartToShareContextAreSeparateHunks() {
        StringBuilder from = new StringBuilder();
        StringBuilder to = new StringBuilder();
        for (int line = 1; line <= 20; line++) {
            from.append(line).append('\n');
            to.append(line == 2 ? "B" : line == 18 ? "R" : String.valueOf(line)).append('\n');
        }

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from.toString(), to.toString());

        assertEquals(List.of("@@ -1,5 +1,5 @@", "@@ -15,6 +15,6 @@"),
                diff.lines().filter(line -> line.startsWith("@@")).toList());
    }

    /**
     * A text and the same text without its final newline are two texts, and a check that calls them
     * different has to be able to show it. Compared as plain lines they are the same list, so the
     * evidence for a verdict of "not formatted" would have been an empty diff.
     */
    @Test
    void aMissingFinalNewlineIsShownAsADifference() {
        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", "a\nb", "a\nb\n");

        assertEquals("""
                --- m.sou
                +++ m.sou (formatted)
                @@ -1,2 +1,2 @@
                 a
                -b
                \\ No newline at end of file
                +b
                """, diff);
    }

    /**
     * Finding which lines two texts share costs the product of their lengths, so a pair large enough
     * is a pair this would answer by exhausting the heap. Past that size it stops looking and shows
     * the two texts whole — still the difference, and still one hunk of a unified diff, just not one
     * that says which lines within it survived.
     */
    @Test
    void aPairTooLargeToCompareLineByLineIsShownWhole() {
        StringBuilder from = new StringBuilder();
        StringBuilder to = new StringBuilder();
        for (int line = 0; line <= 2100; line++) {
            from.append("line ").append(line).append('\n');
            to.append(line % 2 == 0 ? "changed " + line : "line " + line).append('\n');
        }

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from.toString(), to.toString());

        assertEquals(List.of("@@ -1,2101 +1,2101 @@"),
                diff.lines().filter(line -> line.startsWith("@@")).toList());
        assertEquals(List.of(), diff.lines().filter(line -> line.startsWith(" ")).toList());
    }

    /**
     * The bound counts the table that would be filled, which has a row and a column more than the
     * texts have lines. Measured as the product of the two lengths instead, a pair sits under the
     * bound while the table for it is over.
     */
    @Test
    void theBoundCountsTheTableAndNotTheLines() {
        StringBuilder from = new StringBuilder();
        StringBuilder to = new StringBuilder();
        for (int line = 0; line < 2000; line++) {
            from.append("line ").append(line).append('\n');
            // Both ends differ, so nothing is taken off before the bound is measured.
            to.append(line % 2 == 1 && line != 1999 ? "line " + line : "changed " + line)
                    .append('\n');
        }

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from.toString(), to.toString());

        assertEquals(List.of("@@ -1,2000 +1,2000 @@"),
                diff.lines().filter(line -> line.startsWith("@@")).toList());
        assertEquals(List.of(), diff.lines().filter(line -> line.startsWith(" ")).toList());
    }

    /**
     * A pair one line wide on one side reaches the bound too. The lengths multiplied out say such a
     * pair is small, while the table it needs has a row per line of the long side.
     */
    @Test
    void aPairLongOnOneSideOnlyReachesTheBoundAsWell() {
        StringBuilder from = new StringBuilder();
        StringBuilder to = new StringBuilder();
        for (int line = 0; line < 250_000; line++) {
            from.append("line ").append(line).append('\n');
        }
        for (int line = 0; line < 15; line++) {
            to.append(line % 2 == 0 ? "changed " + line : "line " + (line * 1000)).append('\n');
        }

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from.toString(), to.toString());

        assertEquals(List.of("@@ -1,250000 +1,15 @@"),
                diff.lines().filter(line -> line.startsWith("@@")).toList());
        assertEquals(List.of(), diff.lines().filter(line -> line.startsWith(" ")).toList());
    }

    /**
     * The size that decides is the size of what differs, not the size of the file. A file far past
     * the bound that is already canonical everywhere but one line is the ordinary case — a file kept
     * formatted, edited in one place — and it is shown one line at a time like any other.
     */
    @Test
    void aLargeFileThatDiffersInOnePlaceIsShownAtThatPlace() {
        StringBuilder from = new StringBuilder();
        StringBuilder to = new StringBuilder();
        for (int line = 0; line < 5000; line++) {
            from.append("line ").append(line).append('\n');
            to.append(line == 2500 ? "changed" : "line " + line).append('\n');
        }

        String diff = UnifiedDiff.of("m.sou", "m.sou (formatted)", from.toString(), to.toString());

        assertEquals("""
                --- m.sou
                +++ m.sou (formatted)
                @@ -2498,7 +2498,7 @@
                 line 2497
                 line 2498
                 line 2499
                -line 2500
                +changed
                 line 2501
                 line 2502
                 line 2503
                """, diff);
    }
}
