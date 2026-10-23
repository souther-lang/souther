package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.test.ClosedWorldContract;
import souther.test.ReadsTheRepositorysModels;
import org.junit.jupiter.api.Test;

import souther.compiler.DoesNotComeBack;
import souther.compiler.conformance.RepositoryModels;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.ArmObligation;
import souther.compiler.query.ArmSummary;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ObligationDisposition;
import souther.compiler.query.ObligationSummary;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A block prints how many of the obligations it counts a row is at, and everything the difference
 * between the two numbers is made of is under that block.
 *
 * <p>What a reader does with the report is walk from a number to the work it names, so a number
 * whose difference is unaccounted for is a number nothing can be done about. There are three ways
 * to be counted and not met — a gap, a point the rules leave no value at, and a point nobody could
 * decide — and they are told apart because what an author does about them differs: the first is a
 * row to write, the second is nothing anybody can do anything about, and the third is a question
 * this build could not put.
 *
 * <p>Asked of the report's own model and not of its text. What a block prints is a rendering of the
 * account, and the law is about the account: a gap carries exactly one finding, a point left
 * undecided carries none, and both are named. The last is asked of the text, because being named is
 * what the text does.
 *
 * <p>Every arm is populated before anything is asserted about it. A law over three states two of
 * which no source reaches is a law that passes by not applying, and the counts below are what says
 * it does apply.
 */
@ClosedWorldContract
@ReadsTheRepositorysModels
class EveryObligationTheCountHoldsIsMetOrNamedTest {

    /**
     * A model whose one row is past what an observation of it can hold, so no reading of any line
     * comes to an answer and every obligation of it is one nobody could decide.
     *
     * <p>Beside the corpora rather than instead of them. They carry rows that were read, so what
     * they reach is a row at a point and a point read to the end and missed; neither reaches the
     * third state, which is the one this law was written for.
     */
    private static final String TOO_LARGE_TO_OBSERVE = """
            module example.unread

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Item = { a: String, b: String, c: String }
            data Group = { items: List<Item> }

            data Draft = { groups: List<Group>, cost: Amount }
            data Ok = { n: Int }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            let someItems (n: Int): List<Item> =
                List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

            let someGroups (n: Int): List<Group> =
                List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

            example take
                | (Draft { groups = someGroups(64), cost = Amount(0) }) -> Ok { n = 0 }
            """;

    /**
     * A behavior whose one row does not come back, so its arms are the ones nobody could decide.
     *
     * <p>Beside the model above rather than instead of it. That one is past what an observation
     * holds and reaches the third state of a line; a line has no arms, and what reaches the third
     * state of an arm is a row that went somewhere before it stopped.
     */
    private static final String A_ROW_THAT_DOES_NOT_COME_BACK = """
            module example.loop

            data Draft = { n: Int }
            data Done = { n: Int }
            data Small = { n: Int }

            partial let spin (n: Int): Int = spin(n)

            behavior go : (request: Draft) -> Done | Small
                constructs Done, Small

            let go (request) = {
                guard request.n <= 0 else Done { n = spin(request.n) }
                Small { n = request.n }
            }

            example go
                | (Draft { n = 1 }) -> Done { n = 1 }
            """;

    /**
     * A behavior whose rows were all read and go through one arm of two.
     *
     * <p>The corpora cover every arm they have, so nothing in them reaches the state a build
     * refuses over. What a gap needs is a model that leaves one.
     */
    private static final String ONE_ARM_OF_TWO = """
            module example.gate

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Ok = { n: Int }
            data Waiting = { n: Int }

            behavior submit : (request: Draft) -> Ok | Waiting
                constructs Ok, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { n = request.cost.value }
                Ok { n = request.cost.value }
            }

            example submit
                | (Draft { cost = Amount(50) }) -> Ok { n = 50 }
            """;

    /**
     * Two guards that close between them, whose border behind the second has points no row can be
     * written at.
     *
     * <p>Beside the models above rather than instead of them. They reach a row at a point, a point
     * read to the end and missed, and a point nobody could decide; what reaches the fourth is a
     * model whose own rules leave a point of a line it owes no value at all.
     */
    private static final String GUARDS_THAT_CLOSE = """
            module example.closed

            behavior f : (x: Int, y: Int) -> Bool

            let f (x, y) = {
                guard y <= x else false
                guard y >= x + 1 else false
                guard y >= 100 else false

                true
            }
            """;

    @Test
    void everyObligationCountedAndNotMetIsNamedByTheBlockThatCountsIt() {
        List<String> wrong = new ArrayList<>();
        int met = 0;
        int unmet = 0;
        int refuted = 0;
        int undecided = 0;
        int armsMet = 0;
        int armsUnmet = 0;
        int armsUndecided = 0;
        for (Reported reported : reports()) {
            String page = reported.report().human(reported.names());
            // Which block each obligation nobody could decide belongs to, so that what is checked is
            // the block naming its own and not the page holding the right number somewhere — and
            // by which question it is open on, each worded apart, so that a block saying one of
            // them where another is owed is not counted as naming it.
            Map<String, java.util.SequencedMap<String, Integer>> openIn = new LinkedHashMap<>();
            OPEN.forEach(opening -> openIn.put(opening, new java.util.LinkedHashMap<>()));
            // And which block each point the rules leave no value at belongs to, which is the
            // other half of the difference between the two numbers and is named the same way.
            java.util.SequencedMap<String, Integer> refusedIn = new java.util.LinkedHashMap<>();
            for (AdequacyReport.ModuleReport module : reported.report().modules()) {
                ObligationSummary<Adequacy.DeclaredDebt> declared =
                        ObligationSummary.of(module.debts(), each -> each.debt().owed());
                met += declared.met().size();
                unmet += declared.unmet().size();
                refuted += declared.refuted().size();
                undecided += declared.undecided().size();
                for (Adequacy.DeclaredDebt gap : declared.unmet()) {
                    long found = module.declarations().stream()
                            .filter(f -> f.about() instanceof About.APointOfADeclaredBorder(var at)
                                    && at.debt().point().equals(gap.debt().point()))
                            .count();
                    if (found != 1) {
                        wrong.add(reported.name() + " " + module.module() + ": a gap at "
                                + gap.debt().point() + " carries " + found + " findings");
                    }
                }
                String declarationsBlock = module.module() + "/declarations";
                owesNothingYet(openIn, declarationsBlock);
                declared.undecided().forEach(open -> questionsOpen(wrong, reported.name(),
                        open.debt().owed().disposition(), openIn, declarationsBlock));
                refusedIn.put(module.module() + "/declarations", declared.refuted().size());
                for (Adequacy.DeclaredDebt answered : declared.refuted()) {
                    carriesNoFinding(wrong, reported.name(), answered.debt(),
                            module.declarations().stream()
                                    .filter(f -> f.about()
                                            instanceof About.APointOfADeclaredBorder(var at)
                                            && at.debt().point().equals(answered.debt().point()))
                                    .count());
                }
                for (Adequacy.DeclaredDebt open : declared.undecided()) {
                    carriesNoFinding(wrong, reported.name(), open.debt(),
                            module.declarations().stream()
                                    .filter(f -> f.about()
                                            instanceof About.APointOfADeclaredBorder(var at)
                                            && at.debt().point().equals(open.debt().point()))
                                    .count());
                }
                for (AdequacyReport.BehaviorReport behavior : module.behaviors()) {
                    ObligationSummary<BorderObligationPointAssessment> account =
                            ObligationSummary.of(behavior.account(),
                                    BorderObligationPointAssessment::owed);
                    met += account.met().size();
                    unmet += account.unmet().size();
                    refuted += account.refuted().size();
                    undecided += account.undecided().size();
                    for (BorderObligationPointAssessment answered : account.refuted()) {
                        carriesNoFinding(wrong, reported.name(), answered,
                                findingsAbout(behavior, answered));
                    }
                    for (BorderObligationPointAssessment gap : account.unmet()) {
                        long found = findingsAbout(behavior, gap);
                        if (found != 1) {
                            wrong.add(reported.name() + " " + behavior.name() + ": a gap at "
                                    + gap.point() + " carries " + found + " findings");
                        }
                    }
                    for (BorderObligationPointAssessment open : account.undecided()) {
                        carriesNoFinding(wrong, reported.name(), open,
                                findingsAbout(behavior, open));
                    }
                    // The arms of the same behavior, under the same block and held to the same
                    // law. Two accounts and one rule: what a reader does is walk from a number to
                    // the work it names, and a block printing `3/7` with four arms nothing accounts
                    // for is a number nothing can be done about, whichever account it came from.
                    ArmSummary arms = behavior.branch() == null
                            || behavior.branch().measured().made().isEmpty()
                            ? null : behavior.branch().arms();
                    int openArms = 0;
                    if (arms != null) {
                        armsMet += arms.met().size();
                        armsUnmet += arms.unmet().size();
                        openArms = arms.undecided().size();
                        armsUndecided += openArms;
                        if (arms.counted() != arms.met().size() + arms.unmet().size() + openArms) {
                            wrong.add(reported.name() + " " + behavior.name()
                                    + ": the count holds arms in none of the three states");
                        }
                        for (ArmObligation.Counted gap : arms.unmet()) {
                            long found = findingsAbout(behavior, gap);
                            if (found != 1) {
                                wrong.add(reported.name() + " " + behavior.name() + ": an arm at "
                                        + behavior.placeOf(gap.display()) + " carries " + found
                                        + " findings");
                            }
                        }
                        for (ArmObligation.Counted open : arms.undecided()) {
                            if (findingsAbout(behavior, open) != 0) {
                                wrong.add(reported.name() + " " + behavior.name()
                                        + ": an undecided arm at " + behavior.placeOf(open.display())
                                        + " carries a finding");
                            }
                        }
                        for (ArmObligation.NotCounted left : arms.notCounted()) {
                            if (findingsAbout(behavior, left) != 0) {
                                wrong.add(reported.name() + " " + behavior.name()
                                        + ": an arm out of the count at "
                                        + behavior.placeOf(left.display())
                                        + " carries a finding");
                            }
                        }
                    }
                    String block = module.module() + "/" + behavior.name();
                    owesNothingYet(openIn, block);
                    account.undecided().forEach(open -> questionsOpen(wrong, reported.name(),
                            open.owed().disposition(), openIn, block));
                    openIn.get(WHETHER_A_ROW_IS_THERE).merge(block, openArms, Integer::sum);
                    refusedIn.put(module.module() + "/" + behavior.name(),
                            account.refuted().size());
                }
            }
            openIn.forEach((opening, owed) ->
                    saidUnderEachBlock(wrong, reported.name(), page, owed, List.of(opening)));
            saidUnderEachBlock(wrong, reported.name(), page, refusedIn,
                    List.of("· no row can stand at"));
        }

        String reached = "met " + met + ", unmet " + unmet + ", refuted " + refuted
                + ", undecided " + undecided
                + "; arms met " + armsMet + ", unmet " + armsUnmet
                + ", undecided " + armsUndecided;
        assertEquals(List.of(), wrong, "an obligation the count holds is met, marked or named");
        assertTrue(met > 0 && unmet > 0 && refuted > 0 && undecided > 0,
                "every state is reached: " + reached);
        // The arms reach three of their four states here. The fourth is a fork whose declaration
        // says the caller decides and whose rule nothing worked out, and a model of that shape has
        // no rows to read at all — its arms come back unavailable, so no report holds one. What the
        // account does with such an arm is held at the seam it is made at.
        assertTrue(armsMet > 0 && armsUnmet > 0 && armsUndecided > 0,
                "every state an arm reaches here is reached: " + reached);
    }

    /** Whether a row that is written stands at the point; an arm nobody could decide opens so. */
    private static final String WHETHER_A_ROW_IS_THERE = "? undecided whether a row";

    /** Whether a row can be written at the point at all. */
    private static final String WHETHER_ONE_CAN_BE_WRITTEN =
            "? nothing could show a row can be written at the ";

    /** Whether a row gets to the point, where a run may stop on the way. */
    private static final String WHETHER_ONE_GETS_THERE = "? nothing could show a row gets to the ";

    /** Whether a row can be written there where every row there reaches `unreachable`. */
    private static final String WHETHER_ANY_REACHES_IT = "? no row can be written at the ";

    /**
     * The openings of what a point nobody could decide is said to be open on, one line per
     * question — which an author acts on differently, so they are worded apart and a point open
     * on two is named by both.
     */
    private static final List<String> OPEN = List.of(WHETHER_A_ROW_IS_THERE,
            WHETHER_ONE_CAN_BE_WRITTEN, WHETHER_ONE_GETS_THERE, WHETHER_ANY_REACHES_IT);

    /** The opening {@code question} is said with. Over every question there is, so a question
     *  added is a decision here about how it is worded. */
    private static String openingOf(ObligationDisposition.Uncertainty question) {
        return switch (question) {
            case ObligationDisposition.Uncertainty.WhetherARowIsThere _ -> WHETHER_A_ROW_IS_THERE;
            case ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.Stopped _,
                 ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.NothingShowedIt _ ->
                    WHETHER_ONE_CAN_BE_WRITTEN;
            case ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.TheWayThereMayStop _ ->
                    WHETHER_ONE_GETS_THERE;
            case ObligationDisposition.Uncertainty.WhetherARowCanBeWritten
                    .EveryRowReachesAnUnreachable _ -> WHETHER_ANY_REACHES_IT;
        };
    }

    /** {@code block} owing none of any question yet, so that a line of a question it owes none
     *  of is a line too many. */
    private static void owesNothingYet(Map<String, java.util.SequencedMap<String, Integer>> openIn,
                                       String block) {
        openIn.values().forEach(owed -> owed.putIfAbsent(block, 0));
    }

    /** Each question {@code disposition} is open on, owed under {@code block} as a line of its
     *  own opening; a point open on none is one nothing names. */
    private static void questionsOpen(List<String> wrong, String source,
                                      ObligationDisposition disposition,
                                      Map<String, java.util.SequencedMap<String, Integer>> openIn,
                                      String block) {
        List<ObligationDisposition.Uncertainty> open =
                disposition instanceof ObligationDisposition.Undecided it
                        ? it.because().written() : List.of();
        if (open.isEmpty()) {
            wrong.add(source + ": an undecided point open on no question");
        }
        open.forEach(question -> openIn.get(openingOf(question)).merge(block, 1, Integer::sum));
    }

    /** A point nobody could decide carries no finding. */
    private static void carriesNoFinding(List<String> wrong, String source,
                                         BorderObligationPointAssessment open, long findings) {
        if (findings != 0) {
            wrong.add(source + ": an undecided point at " + open.point() + " carries " + findings
                    + " findings");
        }
    }

    /**
     * As many lines of the openings under each block as that block counted of what those openings
     * are written for.
     *
     * <p>Per block and counted, rather than looked for on the page. A block owing ten of them and
     * printing one says the sentence a reader searches for and answers for one of the ten; a page
     * holding the right total says nothing about which block a reader finds them under, and what
     * the law is about is a reader walking from a number to the work it stands for.
     *
     * <p>The page is cut where the blocks are: a module begins at the left margin, and a block of it
     * begins two spaces in, at a behavior this report holds or at the declarations. Nothing else is
     * treated as a beginning, so the declaration names inside the last block stay inside it.
     */
    private static void saidUnderEachBlock(List<String> wrong, String source, String page,
                                           java.util.SequencedMap<String, Integer> owed,
                                           List<String> openings) {
        java.util.Map<String, Integer> said = new java.util.LinkedHashMap<>();
        owed.keySet().forEach(block -> said.put(block, 0));
        String module = null;
        String block = null;
        for (String line : page.lines().toList()) {
            if (!line.isBlank() && !line.startsWith(" ")) {
                module = line.strip().split("\\s+")[0];
                block = null;
            } else if (line.startsWith("  ") && !line.startsWith("   ") && module != null) {
                String named = module + "/" + line.strip().split("\\s+")[0];
                block = owed.containsKey(named) ? named : block;
            } else if (block != null && openings.stream().anyMatch(line.strip()::startsWith)) {
                said.merge(block, 1, Integer::sum);
            }
        }
        owed.forEach((where, counted) -> {
            if (!counted.equals(said.get(where))) {
                wrong.add(source + " " + where + ": " + counted + " counted as " + openings
                        + " and " + said.get(where) + " lines saying so under that block");
            }
        });
    }

    private static long findingsAbout(AdequacyReport.BehaviorReport behavior,
                                      BorderObligationPointAssessment point) {
        return behavior.findings().stream()
                .filter(f -> f.about() instanceof About.APointOfABorder(var at)
                        && at.point().equals(point.point()))
                .count();
    }

    /** The findings about one arm, which are told apart by the arm itself and not by its label:
     *  a behavior with two guards writes two arms called `else`. */
    private static long findingsAbout(AdequacyReport.BehaviorReport behavior, ArmObligation arm) {
        return behavior.findings().stream()
                .filter(f -> f.about() instanceof About.AnArmNoRowGoesThrough(var at)
                        && at.obligation().equals(arm.id()))
                .count();
    }

    /** One report and what to call the sources it is about. */
    private record Reported(String name, AdequacyReport report, SourceRendering names) {}

    private static List<Reported> reports() {
        List<Reported> out = new ArrayList<>();
        // The corpora as every reader of the repository's models takes them, compiled once for all
        // of those.
        RepositoryModels.conformance().forEach((corpus, compilation) -> out.add(new Reported(
                corpus.name(), AdequacyReport.of(compilation),
                new SourceRendering(corpus.names(), compilation.texts()))));
        Compilation unread = Compilation.ofSource(TOO_LARGE_TO_OBSERVE, "Main");
        unread.measure(Adequacy.Asked.fullReport());
        unread.answerEverything();
        out.add(new Reported("example.unread", AdequacyReport.of(unread),
                SourceRendering.namedByIdentity(unread.texts())));
        Compilation stopped = Compilation.ofSource(A_ROW_THAT_DOES_NOT_COME_BACK, "Main");
        stopped.withJvmExampleDeadlines(DoesNotComeBack.overrunningOn(
                DoesNotComeBack.everythingAboutRowsOf("go")));
        stopped.measure(Adequacy.Asked.fullReport());
        stopped.answerEverything();
        out.add(new Reported("example.loop", AdequacyReport.of(stopped),
                SourceRendering.namedByIdentity(stopped.texts())));
        Compilation gate = Compilation.ofSource(ONE_ARM_OF_TWO, "Main");
        gate.measure(Adequacy.Asked.fullReport());
        gate.answerEverything();
        out.add(new Reported("example.gate", AdequacyReport.of(gate),
                SourceRendering.namedByIdentity(gate.texts())));
        Compilation closed = Compilation.ofSource(GUARDS_THAT_CLOSE, "Main");
        closed.measure(Adequacy.Asked.fullReport());
        closed.answerEverything();
        out.add(new Reported("example.closed", AdequacyReport.of(closed),
                SourceRendering.namedByIdentity(closed.texts())));
        return out;
    }
}
