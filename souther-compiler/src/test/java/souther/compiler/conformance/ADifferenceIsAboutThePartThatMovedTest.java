package souther.compiler.conformance;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A difference between two reports is about the part that moved, and not about the parts standing
 * after it.
 *
 * <p>The report is a list of modules holding a list of behaviors holding lists of axes and
 * boundaries, and every one of those members names itself. Matched by position instead, one member
 * leaving reports itself and every member after it, and the reader — who is deciding whether they
 * meant to move that — is handed a list as long as the report and told everything changed.
 *
 * <p>Held on the shapes rather than on the corpus, because the corpus has one arrangement of members
 * and these are claims about what happens when that arrangement changes. Nothing about the corpus
 * removes a behavior.
 */
class ADifferenceIsAboutThePartThatMovedTest {

    private static List<String> between(String was, String now) {
        return WhatMoved.between(was, now);
    }

    /** Two members, and the first one leaves. */
    @Test
    void aMemberThatLeavesIsTheOnlyOneReported() {
        List<String> said = between(
                "{\"modules\":[{\"module\":\"a\",\"rows\":1},{\"module\":\"b\",\"rows\":2}]}",
                "{\"modules\":[{\"module\":\"b\",\"rows\":2}]}");
        assertEquals(1, said.size(), said::toString);
        assertTrue(said.getFirst().startsWith("modules / a:"), said::toString);
        assertTrue(said.getFirst().contains("not answered now"), said::toString);
    }

    /** And the same the other way: one joins, and the member it was written in front of is quiet. */
    @Test
    void aMemberThatJoinsIsTheOnlyOneReported() {
        List<String> said = between(
                "{\"modules\":[{\"module\":\"b\",\"rows\":2}]}",
                "{\"modules\":[{\"module\":\"a\",\"rows\":1},{\"module\":\"b\",\"rows\":2}]}");
        assertEquals(1, said.size(), said::toString);
        assertTrue(said.getFirst().startsWith("modules / a:"), said::toString);
        assertTrue(said.getFirst().contains("was not written down"), said::toString);
    }

    /**
     * The same members written in the other order have not moved.
     *
     * <p>The order a report lists its behaviors in is the order the module declares them, so a
     * reordering is a real change to the source and not to what was answered about it — and what
     * was answered is what these documents are for.
     */
    @Test
    void theSameMembersInAnotherOrderHaveNotMoved() {
        assertEquals(List.of(), between(
                "{\"modules\":[{\"module\":\"a\",\"rows\":1},{\"module\":\"b\",\"rows\":2}]}",
                "{\"modules\":[{\"module\":\"b\",\"rows\":2},{\"module\":\"a\",\"rows\":1}]}"));
    }

    /** A member that changed is reported under its own name, however it is ordered. */
    @Test
    void aMemberThatChangedIsReportedUnderItsName() {
        List<String> said = between(
                "{\"modules\":[{\"module\":\"a\",\"rows\":1},{\"module\":\"b\",\"rows\":2}]}",
                "{\"modules\":[{\"module\":\"b\",\"rows\":9},{\"module\":\"a\",\"rows\":1}]}");
        assertEquals(List.of("modules / b / rows: was 2, now 9"), said);
    }

    /** Nested: a behavior of a module, an axis of a behavior. */
    @Test
    void aPathIsBuiltFromEveryNameOnTheWayDown() {
        List<String> said = between(
                "{\"modules\":[{\"module\":\"m\",\"behaviors\":[{\"name\":\"f\",\"partition\":"
                        + "{\"axes\":[{\"axis\":\"f/x\",\"covered\":[\"A\",\"B\"]}]}}]}]}",
                "{\"modules\":[{\"module\":\"m\",\"behaviors\":[{\"name\":\"f\",\"partition\":"
                        + "{\"axes\":[{\"axis\":\"f/x\",\"covered\":[\"A\"]}]}}]}]}");
        assertEquals(List.of("modules / m / behaviors / f / partition / axes / f/x / covered:"
                + " no longer holds \"B\""), said);
    }

    /**
     * Members that name nothing are matched by position, which is all there is to match them by.
     *
     * <p>Said rather than left to be found: a report that grew a list of anonymous objects would go
     * on being compared, and the reader would be told about positions. What that costs is the
     * reason the identities are read off the document in the first place.
     */
    @Test
    void membersThatNameNothingAreMatchedByPosition() {
        List<String> said = between(
                "{\"xs\":[{\"a\":1},{\"a\":2}]}",
                "{\"xs\":[{\"a\":2}]}");
        assertTrue(said.stream().anyMatch(s -> s.contains("xs: held 2 and now holds 1")),
                said::toString);
        assertTrue(said.stream().anyMatch(s -> s.startsWith("xs[0]")), said::toString);
    }

    /** And so are members that name the same thing twice: a duplicate leaves no way to say which
     *  of them a difference is about. */
    @Test
    void duplicateNamesAreMatchedByPosition() {
        List<String> said = between(
                "{\"xs\":[{\"name\":\"a\",\"v\":1},{\"name\":\"a\",\"v\":2}]}",
                "{\"xs\":[{\"name\":\"a\",\"v\":1},{\"name\":\"a\",\"v\":9}]}");
        assertEquals(List.of("xs[1] / v: was 2, now 9"), said);
    }

    /** A list of plain values is said as what joined it and what left it. */
    @Test
    void aListOfValuesIsSaidAsWhatJoinedAndWhatLeft() {
        assertEquals(List.of("covered: no longer holds \"B\"", "covered: now holds \"C\""),
                between("{\"covered\":[\"A\",\"B\"]}", "{\"covered\":[\"C\",\"A\"]}"));
    }

    /** An empty list and a list of one are not compared by position either. */
    @Test
    void aMemberJoiningAnEmptyListIsReportedByName() {
        List<String> said = between("{\"modules\":[]}",
                "{\"modules\":[{\"module\":\"a\",\"rows\":1}]}");
        assertEquals(1, said.size(), said::toString);
        assertTrue(said.getFirst().startsWith("modules / a"), said::toString);
    }
}
