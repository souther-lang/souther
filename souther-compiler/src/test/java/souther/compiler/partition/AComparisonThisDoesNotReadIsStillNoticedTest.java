package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.TermPath;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A position this could not read a line at is not a position the model draws no line through.
 *
 * <p>What a reader does not read, it reports as absent, and the two are different things to tell an
 * author. This one names the positions a comparison in the body is written about and this did not
 * turn into a line, so that whatever answers for the position afterwards is not left inferring the
 * model from an empty list.
 *
 * <p>Noticing only. Nothing here is a threshold, and nothing derived from this may become one: which
 * arm witnesses a comparison inside a conjunction is a separate question, and a line recorded without
 * it would be an obligation nobody could meet.
 */
class AComparisonThisDoesNotReadIsStillNoticedTest {

    private static GuardThresholds.Guards read(String condition) {
        return read("n: Count", condition);
    }

    private static GuardThresholds.Guards read(String parameter, String condition) {
        String source = """
                module example.guarded

                data Count = Int
                    invariant range = value >= 0 && value <= 10

                data Pair = { x: Int, y: Int }

                data Low
                data High

                behavior pick : (PARAMETER) -> Low | High

                let pick (NAME) =
                    if CONDITION
                        then High
                        else Low
                """.replace("PARAMETER", parameter)
                        .replace("NAME", parameter.substring(0, parameter.indexOf(':')).trim())
                        .replace("CONDITION", condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + condition);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("pick")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("pick");
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies());
        return GuardThresholds.of("pick", body, plan,
                compilation.db().ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get("pick"), symbols);
    }

    /** A comparison this reads is not also reported as one it did not. */
    @Test
    void aComparisonThatBecameALineIsNotReportedAsUnread() {
        GuardThresholds.Guards guards = read("n.value <= 5");

        assertEquals(1, guards.thresholds().size());
        assertEquals(List.of(), guards.unread());
    }

    /** A comparison inside a conjunction is read, so it is not one this did not read. */
    @Test
    void aComparisonInsideAConjunctionIsReadRatherThanNamed() {
        GuardThresholds.Guards guards = read("n.value >= 1 && n.value <= 5");

        assertEquals(2, guards.thresholds().size(), guards.thresholds().toString());
        assertEquals(List.of(), guards.unread());
    }

    /**
     * A comparison whose operator draws no line, which is what an equality is.
     *
     * <p>Read as far as naming a position and no further. Whether the two classes an equality divides
     * the values into can be held at all is a separate question; that they are divided is this one.
     */
    @Test
    void anEqualityIsReadRatherThanNamed() {
        GuardThresholds.Guards guards = read("n.value == 3");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.singled().size(), guards.singled().toString());
    }

    /**
     * A string is read, which it was not.
     *
     * <p>It is ordered — the comparison typechecks and the branch is real — and the only thing about
     * it out of reach is the value below the line, which is what a carrier with no step already
     * says. Left unread, the position came back saying no line could be drawn on values the language
     * orders.
     */
    @Test
    void aLineDrawnOnAStringIsRead() {
        GuardThresholds.Guards guards = read("at: String", "at < \"2026-01\"");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.thresholds().size(), guards.thresholds().toString());
    }

    /**
     * A date-time is read, which a date already was.
     *
     * <p>Two temporal types differing only in resolution answered differently, and what the
     * unsettled step decides is the value beside a line rather than whether there is one.
     */
    @Test
    void aLineDrawnOnADateTimeIsRead() {
        GuardThresholds.Guards guards =
                read("at: DateTime", "at < DateTime(\"2026-01-01T00:00:00\")");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.thresholds().size(), guards.thresholds().toString());
    }

    /**
     * A time of day is read, which it was not.
     *
     * <p>Ordered and held to the second, so the line and the value beside it are both there. What
     * was missing was the way back from a count, which is a conversion and not a fact about the
     * values.
     */
    @Test
    void aLineDrawnOnATimeIsRead() {
        GuardThresholds.Guards guards = read("at: Time", "at < Time(\"16:00:00\")");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.thresholds().size(), guards.thresholds().toString());
    }

    /** A moment is read, at its own unit. */
    @Test
    void aLineDrawnOnAnInstantIsRead() {
        GuardThresholds.Guards guards =
                read("at: Instant", "at < Instant(\"2026-01-01T00:00:00Z\")");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.thresholds().size(), guards.thresholds().toString());
    }

    /**
     * Two comparisons about one position are two findings, however alike they read.
     *
     * <p>Asked of the position, the second was dropped as a repeat of the first — and what an
     * author is owed is one line per rule they would have to rewrite. The two here are stopped by
     * the same limit at the same position and are two things to do, which is the whole of issue
     * the same defect seen from inside one condition.
     */
    @Test
    void twoComparisonsAboutOnePositionAreTwoFindings() {
        List<UnreadRule> unread = read("at: Int",
                "Int.multiply(at, at) < 4 || Int.multiply(at, at) > 9").unread();

        assertEquals(List.of(new Said(TermPath.of("at"), new BlockReason.UnreadComparisonForm()),
                        new Said(TermPath.of("at"), new BlockReason.UnreadComparisonForm())),
                said(unread));
        assertEquals(2, unread.stream().map(UnreadRule::rule).distinct().count(),
                () -> "two comparisons are two rules: " + unread);
    }

    /**
     * And the rule is named, by what tells one from another and by what a reader looks for.
     *
     * <p>The position was all this used to carry, so a report could say a rule about `+p.x+` went
     * unread and name no rule. What identifies a comparison is the behavior it is written in and
     * the construct the author wrote; what finds it is where it is written. Neither is the
     * plan\u0027s: a condition nothing can be measured about is numbered nowhere, and the model
     * states the rule regardless.
     */
    @Test
    void aFindingNamesTheComparisonThatWentUnread() {
        UnreadRule said = read("p: Pair", "Int.multiply(p.x, p.x) < 10").unread().getFirst();

        assertInstanceOf(RuleRef.Comparison.class, said.rule());
        RuleCitation.WrittenAt cited = assertInstanceOf(RuleCitation.WrittenAt.class, said.cited());
        assertInstanceOf(souther.compiler.diag.Citation.Written.class, cited.at(),
                "a rule with no name is found where it is written, which this compile has a file "
                        + "for");
    }

    /**
     * A position named inside an expression the reader does not model is still named.
     *
     * <p>Discovery and derivation are different questions and must not share a reader. What decides
     * whether a line can be drawn is whether the number compared is one the arithmetic reads; what
     * decides whether the model says anything here is whether a comparison mentions the position at
     * all. Asked of the first, a position inside an expression this cannot read reports a position
     * the model divides no way, two tokens from a comparison about it.
     *
     * <p>A variable product, because that is what is left outside the fragment: {@code p.x + 1 < 10}
     * is {@code p.x <= 9} and is read, and a factor that moves with the row is not a form this has a
     * rule for.
     */
    @Test
    void aPositionNamedInsideAnExpressionIsStillNoticed() {
        assertEquals(List.of(new Said(TermPath.of("p").then("x"),
                        new BlockReason.UnreadComparisonForm())),
                said(read("p: Pair", "Int.multiply(p.x, p.x) < 10").unread()));
    }

    /**
     * Two positions compared with each other, which is a relation and not a partition of either.
     *
     * <p>Nothing is wrong with the carrier — both are `+Int+`, ordered, and a line drawn on either
     * against a number would be read. What is missing is a class that is about two positions at
     * once, and saying "no line can be drawn on these values" would send a reader after a carrier.
     */
    @Test
    void twoPositionsComparedWithEachOtherSayWhichLimitThatIs() {
        assertEquals(List.of(
                        new Said(TermPath.of("p").then("x"),
                                new BlockReason.ComparisonBetweenPositions()),
                        new Said(TermPath.of("p").then("y"),
                                new BlockReason.ComparisonBetweenPositions())),
                said(read("p: Pair", "p.x < p.y").unread()));
    }

    /**
     * A line read at a position does not stand for every comparison about it.
     *
     * <p>One position can carry more than one statement, and reading one of them says nothing about
     * the rest. Kept per position, a threshold on `+p.x+` swallowed the comparison beside it that
     * nothing could read — which is "some result exists, therefore the reading is complete", the
     * inference this whole issue is about.
     */
    @Test
    void aLineReadAtAPositionDoesNotSwallowWhatWasNotReadThere() {
        GuardThresholds.Guards guards =
                read("p: Pair", "p.x <= 5 && Int.multiply(p.x, p.x) < 10");

        assertEquals(1, guards.thresholds().size(), guards.thresholds().toString());
        assertEquals(List.of(new Said(TermPath.of("p").then("x"),
                        new BlockReason.UnreadComparisonForm())),
                said(guards.unread()));
    }

    /**
     * A relation stays a relation when one side is written with something added to it.
     *
     * <p>What `+p.x < p.y * p.y+` needs is a class about two positions, exactly as
     * `+p.x < p.y+` does. Read off how far the derivation got, the second side stops being a
     * position at all and the answer becomes the carrier — which is a different piece of work and
     * not the one that is owed.
     *
     * <p>`+p.x < p.y + 1+` is not this case any more. It is `+p.x - p.y < 1+`, a line where the two
     * stand one apart, and it is drawn — so what is left here is a relation the arithmetic reads
     * nothing out of at all.
     */
    @Test
    void aRelationWithArithmeticOnOneSideIsStillARelation() {
        assertEquals(List.of(
                        new Said(TermPath.of("p").then("x"),
                                new BlockReason.ComparisonBetweenPositions()),
                        new Said(TermPath.of("p").then("y"),
                                new BlockReason.ComparisonBetweenPositions())),
                said(read("p: Pair", "p.x < Int.multiply(p.y, p.y)").unread()));
    }

    /**
     * A position whose carrier is fine, against a right-hand side this does not read.
     *
     * <p>`+Int.min(1, 2)+` is not a form a threshold is read out of, and that is the whole of what
     * stopped the line. Nothing is wrong with `+p.x+`: it is an `+Int+`, a carrier lines are drawn
     * on all through this file. Read off the side that did name a position, the answer becomes the
     * carrier and sends a reader after a domain that is already there.
     */
    @Test
    void aReadableCarrierAgainstAnUnreadableSideIsNotACarrierProblem() {
        assertEquals(List.of(new Said(TermPath.of("p").then("x"),
                        new BlockReason.UnreadComparisonForm())),
                said(read("p: Pair", "p.x < Int.min(1, 2)").unread()));
    }

    /**
     * What a finding says about a position, apart from which rule said it.
     *
     * <p>Spelled out where every entry is about one rule and what is being read is the position and
     * the limit. Which rule it was has its own test, because it is its own question.
     */
    private record Said(TermPath at, BlockReason why) {}

    private static List<Said> said(List<UnreadRule> unread) {
        return unread.stream().map(each -> new Said(each.at(), each.why())).toList();
    }
}
