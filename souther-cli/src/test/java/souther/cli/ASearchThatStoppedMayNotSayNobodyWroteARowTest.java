package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point a stopped search found nothing at is undecided, and one found at is met.
 *
 * <p>The readings of a row are the elements chosen at each step its positions take, and a row
 * holding sequences inside sequences has more of them than one point is tried against. What such a
 * walk may conclude is not symmetric: a reading standing at the point settles the point however few
 * were tried, and a point no tried reading stands at is a point nothing stands at only where there
 * were no others to try.
 *
 * <p><b>The four below are one model with the value moved.</b> Which reading holds the value the
 * line is at is the row's business and nothing about the model, so a verdict that turns on it is a
 * verdict about this compiler's walk. The pair that moves it is what says so: the same row, the
 * same element count, and the answer was a gap a strict build refuses over in one and a met point
 * in the other.
 */
class ASearchThatStoppedMayNotSayNobodyWroteARowTest {

    /** More readings than one point is tried against, which takes a step inside a step. */
    private static final int WIDE = 17;

    /** Fewer, so that the same shape with the value last is walked to the end. */
    private static final int NARROW = 8;

    /** Long enough that observing the row is what stops, which is the other limit. */
    private static final int LONGER_THAN_A_ROW_IS_OBSERVED_AT = 300;

    private static final String THE_POINT = "ON point value = 20";

    @Test
    void aReadingThatStandsAtThePointSettlesItHoweverManyWereTried() throws Exception {
        String report = run(aLeague(rows(WIDE, WIDE, 0, 0)));

        assertEquals(List.of(), saidAbout(report),
                "the value is in the first reading tried, and a walk that stops after finding it"
                        + " has found it");
    }

    @Test
    void andAPointNoReadingStandsAtIsAGapWhereThereWereNoOthersToTry() throws Exception {
        String report = run(aLeague(rows(NARROW, NARROW, NOWHERE, NOWHERE)));

        assertEquals(List.of("! no row is at the " + THE_POINT + " (invariant Score #1)"),
                saidAbout(report),
                "every reading the steps allow was tried and none stands there, which is the row"
                        + " nobody wrote");
    }

    @Test
    void andIsUndecidedWhereTheReadingsRanPastWhatAPointIsTriedAgainst() throws Exception {
        String report = run(aLeague(rows(WIDE, WIDE, WIDE - 1, WIDE - 1)));

        assertEquals(List.of("? undecided whether a row is at the " + THE_POINT
                        + " (invariant Score #1), and the readings of the row ran past what one"
                        + " point is tried against, so the rest of them were never tried"),
                saidAbout(report),
                "the value is in a reading nobody made, and a walk that did not make it cannot say"
                        + " nobody wrote the row");
    }

    @Test
    void andSaysBothWhereOneRowStoppedTheReadingsAndAnotherStoppedTheObserving() throws Exception {
        String report = run(aLeague(rows(WIDE, WIDE, NOWHERE, NOWHERE),
                rows(1, LONGER_THAN_A_ROW_IS_OBSERVED_AT, NOWHERE, NOWHERE)));

        List<String> said = saidAbout(report);
        assertEquals(1, said.size(), () -> "one point, one sentence: " + said);
        assertTrue(said.getFirst().contains("the observation of it was stopped by a limit"),
                () -> "what the reading that was made met is said: " + said);
        assertTrue(said.getFirst().contains("the readings of the row ran past what one point is"
                        + " tried against"),
                () -> "and the readings nobody made are said beside it, because a reader raising"
                        + " one figure has not reached what the other stopped: " + said);
    }

    /** No element of the row is at the point, which is what a row with no value there is. */
    private static final int NOWHERE = -1;

    /** One league: teams of scores, with the value at one element of one of them or at none. */
    private static String rows(int teams, int scores, int whichTeam, int whichScore) {
        List<String> all = new ArrayList<>();
        for (int team = 0; team < teams; team++) {
            List<String> one = new ArrayList<>();
            for (int score = 0; score < scores; score++) {
                one.add(team == whichTeam && score == whichScore ? "Score(20)" : "Score(1)");
            }
            all.add("Team { scores = [ " + String.join(", ", one) + " ] }");
        }
        return "League { teams = [ " + String.join(", ", all) + " ] }";
    }

    /** The model, with one example row per league handed in. */
    private static String aLeague(String... leagues) {
        List<String> written = new ArrayList<>();
        for (int at = 0; at < leagues.length; at++) {
            written.add("    | \"row " + at + "\" : (" + leagues[at]
                    + ") -> Answer { ok = true }");
        }
        return """
                module m

                data Score = Int
                    invariant value >= 0 && value <= 20

                data Team = { scores: List<Score> }
                data League = { teams: List<Team> }
                data Answer = { ok: Bool }

                behavior f : (l: League) -> Answer

                example f
                %s
                """.formatted(String.join("\n", written));
    }

    /** What the report says about the point the value is at, and nothing about any other. */
    private static List<String> saidAbout(String report) {
        List<String> said = new ArrayList<>();
        for (String line : report.split("\n")) {
            if (line.contains(THE_POINT)) {
                said.add(line.strip());
            }
        }
        return said;
    }

    private static String run(String source) throws Exception {
        Path file = Files.createTempDirectory("souther-readings").resolve("m.sou");
        Files.writeString(file, source);
        PrintStream out = System.out;
        PrintStream err = System.err;
        ByteArrayOutputStream said = new ByteArrayOutputStream();
        System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(new ByteArrayOutputStream(), true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString()});
        } finally {
            System.setOut(out);
            System.setErr(err);
        }
        return said.toString(StandardCharsets.UTF_8);
    }
}
