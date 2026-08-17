package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a witness is projected through is its own unit's, gathered once, and it says what sweeping
 * the whole file said.
 *
 * <p>Two of the projections used to read everything to answer about one unit. A group's witness is
 * about the opportunities that group settles and a layout has one at every place any group could
 * break; a level's witness is about the lines written under that level and the canonical form's
 * lines are the whole file's. So both are gathered under the unit that is asked about, and what is
 * held here is that gathering them changed no answer.
 *
 * <p>Held against the sweep rather than against a second statement of what the answers ought to be.
 * The sweep is what the rules were written against, and a {@link Repair.Round} built from it is a
 * round the projection cannot tell from the one it is given — so the two are handed to the same
 * projection and the edits are compared.
 *
 * <p>Over the corpus, and over sources that depart at every group and every level. The corpus
 * departs at a few of its units, which is the case where a sweep and a gathering agree by having
 * almost nothing to disagree about; a source written down the page where the canonical form writes
 * it flat, or indented two columns where it writes four, is the case the gathering was made for.
 */
class AWitnessIsProjectedThroughItsOwnUnitAndNotTheWholeFileTest {

    /**
     * A source that departs at every group it has: each declaration is written down the page where
     * the canonical form writes it on one line.
     */
    private static String departingAtEveryGroup(int declarations) {
        StringBuilder out = new StringBuilder("module m\n\nlet g (a: Int, b: Int): Int = a + b\n");
        for (int i = 0; i < declarations; i++) {
            out.append("""

                    let f%d (a: Int): Int = g(
                        a,
                        a
                    )
                    """.formatted(i));
        }
        return out.toString();
    }

    /**
     * A source that departs at every level it has: each declaration is written down the page, as the
     * canonical form writes it, and indented two columns where it writes four.
     */
    private static String departingAtEveryLevel(int declarations) {
        StringBuilder out = new StringBuilder("module m\n");
        for (int i = 0; i < declarations; i++) {
            out.append("""

                    data D%d =
                      { aRatherLongFieldName: Int
                      , anotherRatherLongFieldName: Int
                      , yetAnotherRatherLongFieldName: Int
                      }
                    """.formatted(i));
        }
        return out.toString();
    }

    /**
     * A source that departs at a level with levels under it: the outer block is indented two
     * columns where the canonical form writes four, and the block nested inside it is written at a
     * column of its own.
     *
     * <p>The level a witness names is not always the innermost one on its lines. A level that moves
     * takes what is nested inside it along, so the lines its repair writes include the deeper ones —
     * and a source whose every departure is at an innermost level asks nothing about that.
     */
    private static String departingAtALevelWithLevelsUnderIt(int declarations) {
        StringBuilder out = new StringBuilder("module m\n");
        for (int i = 0; i < declarations; i++) {
            out.append("""

                    let f%d (a: Int): Int = {
                      let b = {
                            let c = a + 1
                            c
                        }
                      b
                    }
                    """.formatted(i));
        }
        return out.toString();
    }

    /** The corpus, and the three shapes the gathering was made for. */
    private static List<String> sources() {
        List<String> out = new ArrayList<>(WhatGoesBetweenTwoTokensOnALineTest.corpus());
        out.add(departingAtEveryGroup(6));
        out.add(departingAtEveryLevel(6));
        out.add(departingAtALevelWithLevelsUnderIt(6));
        return out;
    }

    /** Every family's witnesses about one source, as a report asks for them. */
    private static List<Witness> witnesses(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing) {
        List<Witness> out = new ArrayList<>();
        List<Family> families = List.of(Witnesses::tokens, Witnesses::spacing,
                Witnesses::separation, Witnesses::indentation, Witnesses::forced,
                Witnesses::settled, Witnesses::conditional, Witnesses::comments,
                Witnesses::lineEnds);
        for (Family family : families) {
            try {
                out.addAll(family.of(source, canonical, pairing));
            } catch (Witnesses.NoCorrespondence _) {
                // this family has nothing to ask about this source, as a report would find
            }
        }
        return out;
    }

    private interface Family {
        List<Witness> of(String source, Formatter.CanonicalForm canonical,
                Witnesses.Pairing pairing);
    }

    /** Which opportunities a group settles, by sweeping the layout for the ones that name it. */
    private static List<Opportunity> sweptTo(Layout layout, Doc.GroupRef group) {
        List<Opportunity> out = new ArrayList<>();
        for (Opportunity o : layout.opportunities()) {
            if (o.settledBy() == group) {
                out.add(o);
            }
        }
        return out;
    }

    /** Which lines are written under a level, by sweeping the canonical form's lines. */
    private static List<Witnesses.CanonicalLine> sweptUnder(List<Witnesses.CanonicalLine> lines,
            Doc.NestRef level) {
        List<Witnesses.CanonicalLine> out = new ArrayList<>();
        for (Witnesses.CanonicalLine line : lines) {
            if (line.under().contains(level)) {
                out.add(line);
            }
        }
        return out;
    }

    /** Every group any opportunity of a layout names, in the order they are met. */
    private static List<Doc.GroupRef> groupsOf(Layout layout) {
        Set<Doc.GroupRef> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        List<Doc.GroupRef> out = new ArrayList<>();
        for (Opportunity o : layout.opportunities()) {
            if (seen.add(o.settledBy())) {
                out.add(o.settledBy());
            }
        }
        return out;
    }

    /** Every level any line of a canonical form is written under, in the order they are met. */
    private static List<Doc.NestRef> levelsOf(List<Witnesses.CanonicalLine> lines) {
        Set<Doc.NestRef> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        List<Doc.NestRef> out = new ArrayList<>();
        for (Witnesses.CanonicalLine line : lines) {
            for (Doc.NestRef level : line.under()) {
                if (seen.add(level)) {
                    out.add(level);
                }
            }
        }
        return out;
    }

    /**
     * A group's opportunities are the ones sweeping the layout finds, in the order it finds them.
     *
     * <p>The gathering says which they are, and that is the whole of what it says: the repair sorts
     * them by the adjacency they stand at before writing anything. Held in order anyway, because a
     * gathering that met them in another order is a gathering that met other opportunities in every
     * case this can tell apart, and reading the difference off the sequence says which.
     */
    @Test
    void aGroupsOpportunitiesAreTheOnesTheSweepFinds() {
        int settlingSeveral = 0;
        for (String source : sources()) {
            Formatter.CanonicalForm canonical =
                    Formatter.canonicalize(CstParser.parse(source).root());
            Repair.Round round = new Repair.Round(source, canonical,
                    new Witnesses.Pairing(source, canonical));
            for (Doc.GroupRef group : groupsOf(canonical.layout())) {
                List<Opportunity> swept = sweptTo(canonical.layout(), group);
                assertEquals(swept, round.settling().get(group),
                        "the opportunities gathered under a group of " + head(source));
                if (swept.size() > 1) {
                    settlingSeveral++;
                }
            }
        }
        assertTrue(settlingSeveral > 0,
                "no group of any source settles more than one opportunity, so gathering them under"
                        + " the group is a gathering of nothing");
    }

    /**
     * And a group that settles none of them has none, rather than the layout's.
     *
     * <p>Where a gathering has no entry, what a sweep found was nothing — so the projection reads
     * nothing, and not every opportunity the file has.
     */
    @Test
    void andAGroupThatSettlesNoneOfThemHasNone() {
        String source = departingAtEveryGroup(2);
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        Repair.Round round = new Repair.Round(source, canonical,
                new Witnesses.Pairing(source, canonical));

        Doc.GroupRef settlingNothing = new Doc.GroupRef();
        assertEquals(List.of(), sweptTo(canonical.layout(), settlingNothing));
        assertNull(round.settling().get(settlingNothing));
        assertTrue(!canonical.layout().opportunities().isEmpty(),
                "the layout has no opportunity, so this asks nothing");
    }

    /**
     * The lines under a level are the ones sweeping the canonical form's lines finds, in the order
     * it finds them.
     *
     * <p>Every level the line is written under and not only the innermost. A level that moves takes
     * what is nested inside it along, so a line four levels deep is under four of them and a
     * gathering that filed it under one would leave the outer three writing nothing for it.
     *
     * <p>In order, which this one does rest on: the repair keeps the first line it meets at each of
     * the source's line starts, so a level's lines met in another order are another set of edits.
     */
    @Test
    void theLinesUnderALevelAreTheOnesTheSweepFinds() {
        int underSeveral = 0;
        int levelsWithSeveralLines = 0;
        for (String source : sources()) {
            Formatter.CanonicalForm canonical =
                    Formatter.canonicalize(CstParser.parse(source).root());
            Witnesses.Pairing pairing = new Witnesses.Pairing(source, canonical);
            List<Witnesses.CanonicalLine> lines = Witnesses.lines(source, canonical, pairing);
            Repair.Round round = new Repair.Round(source, canonical, pairing);
            for (Doc.NestRef level : levelsOf(lines)) {
                List<Witnesses.CanonicalLine> swept = sweptUnder(lines, level);
                assertEquals(swept, round.under().get(level),
                        "the lines gathered under a level of " + head(source));
                if (swept.size() > 1) {
                    levelsWithSeveralLines++;
                }
            }
            for (Witnesses.CanonicalLine line : lines) {
                if (line.under().size() > 1) {
                    underSeveral++;
                }
            }
        }
        assertTrue(underSeveral > 0, "no line of any source is written under more than one level");
        assertTrue(levelsWithSeveralLines > 0, "no level of any source holds more than one line");
    }

    /**
     * And the projection says what it said when it swept.
     *
     * <p>The two rounds differ in nothing but how the two gatherings were built, so the edits a
     * witness comes to are the same edits or the gathering changed an answer. Every family is
     * projected, not only the two that read a gathering: what the round holds is read by name, and a
     * family reading the wrong one is what this would find.
     */
    @Test
    void andTheProjectionSaysWhatItSaidWhenItSwept() {
        int conditional = 0;
        int indentation = 0;
        int overADeeperLine = 0;
        int edits = 0;
        for (String source : sources()) {
            Formatter.CanonicalForm canonical =
                    Formatter.canonicalize(CstParser.parse(source).root());
            Witnesses.Pairing pairing = new Witnesses.Pairing(source, canonical);
            List<Witnesses.CanonicalLine> lines = Witnesses.lines(source, canonical, pairing);

            Map<Doc.GroupRef, List<Opportunity>> settling = new IdentityHashMap<>();
            for (Doc.GroupRef group : groupsOf(canonical.layout())) {
                settling.put(group, sweptTo(canonical.layout(), group));
            }
            Map<Doc.NestRef, List<Witnesses.CanonicalLine>> under = new IdentityHashMap<>();
            for (Doc.NestRef level : levelsOf(lines)) {
                under.put(level, sweptUnder(lines, level));
            }
            Repair.Round swept = new Repair.Round(source, canonical, pairing, settling, under);
            Repair.Round gathered = new Repair.Round(source, canonical, pairing);

            for (Witness w : witnesses(source, canonical, pairing)) {
                List<Repair.Edit> was = Repair.of(swept, w);
                assertEquals(was, Repair.of(gathered, w),
                        "the stretches " + w.getClass().getSimpleName() + " comes to in "
                                + head(source));
                edits += was.size();
                if (w instanceof Witness.Conditional || w instanceof Witness.RunTogether) {
                    conditional++;
                }
                if (w instanceof Witness.Indentation i) {
                    indentation++;
                    for (Witnesses.CanonicalLine line : sweptUnder(lines, i.unit().inner())) {
                        if (line.under().get(line.under().size() - 1) != i.unit().inner()) {
                            overADeeperLine++;
                        }
                    }
                }
            }
        }
        assertTrue(conditional > 0, "no source has a witness that reads a group's opportunities");
        assertTrue(indentation > 0, "no source has a witness that reads a level's lines");
        assertTrue(overADeeperLine > 0,
                "every level a witness names is the innermost one on its lines, so nothing here"
                        + " asks whether a line is gathered under the levels above it too");
        assertTrue(edits > 0, "the projection came to no stretch at all, so this compares nothing");
    }

    /**
     * And a round hands back one list per witness, in the order it was asked about them.
     *
     * <p>What a report wants of a witness besides its expectation is where in the source it lands,
     * which is where the first stretch it comes to begins. It reads that off the list of the witness
     * it is about, so a round that handed back the lists in another order, or fewer of them than it
     * was asked about, would put every deviation past that point at another rule's place.
     */
    @Test
    void andARoundHandsBackOneListPerWitnessInOrder() {
        String source = departingAtEveryGroup(3);
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        Witnesses.Pairing pairing = new Witnesses.Pairing(source, canonical);
        List<Witness> witnesses = witnesses(source, canonical, pairing);
        Repair.Round round = new Repair.Round(source, canonical, pairing);

        List<List<Repair.Edit>> each = Repair.each(source, canonical, pairing, witnesses);
        assertEquals(witnesses.size(), each.size());
        assertTrue(witnesses.size() > 1, "one witness, so an order is not being held to anything");
        for (int i = 0; i < witnesses.size(); i++) {
            assertEquals(Repair.of(round, witnesses.get(i)), each.get(i),
                    "the stretches witness " + i + " comes to");
        }
    }

    /**
     * And repairing what the rules say about these three sources writes their canonical form.
     *
     * <p>{@link RepairingWhatTheRulesSayWritesTheCanonicalFormTest} holds this of every source the
     * repository has, and none of them departs at more than a handful of its units — which is the
     * case a projection that reads one unit and one that reads the file agree on. So the three
     * written here are held to it too, and {@link Deviations.Report#whole} is the statement: a source
     * it is true of is one where the repair reached the canonical form and every difference on the
     * way was named by a rule.
     */
    @Test
    void andRepairingADenseSourceStillWritesItsCanonicalForm() {
        for (String source : List.of(departingAtEveryGroup(6), departingAtEveryLevel(6),
                departingAtALevelWithLevelsUnderIt(6))) {
            Deviations.Report report = Deviations.of(source);
            assertTrue(report.whole(),
                    "repairing what the rules say about " + head(source)
                            + " does not write its canonical form");
            assertTrue(!report.deviations().isEmpty(),
                    head(source) + " is already canonical, so nothing was projected");
        }
    }

    /** The first line of a source, to say which one an assertion is about. */
    private static String head(String source) {
        int newline = source.indexOf('\n');
        return "`" + (newline < 0 ? source : source.substring(0, newline)) + "`";
    }
}
