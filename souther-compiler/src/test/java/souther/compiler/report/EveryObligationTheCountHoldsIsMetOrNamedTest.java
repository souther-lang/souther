package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ObligationSummary;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A block prints how many of the obligations it counts a row is at, and everything the difference
 * between the two numbers is made of is under that block.
 *
 * <p>What a reader does with the report is walk from a number to the work it names, so a number
 * whose difference is unaccounted for is a number nothing can be done about. There are two ways to
 * be counted and not met — a gap, and a point nobody could decide — and they are told apart because
 * what an author does about them differs: one is a row to write, and the other is a question this
 * build could not put.
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

    @Test
    void everyObligationCountedAndNotMetIsNamedByTheBlockThatCountsIt() {
        List<String> wrong = new ArrayList<>();
        int met = 0;
        int unmet = 0;
        int undecided = 0;
        for (Reported reported : reports()) {
            String page = reported.report().human(reported.names());
            // Which block each obligation nobody could decide belongs to, so that what is checked is
            // the block naming its own and not the page holding the right number somewhere.
            java.util.SequencedMap<String, Integer> openIn = new java.util.LinkedHashMap<>();
            for (AdequacyReport.ModuleReport module : reported.report().modules()) {
                ObligationSummary<Adequacy.DeclaredDebt> declared =
                        ObligationSummary.of(module.debts(), each -> each.debt().owed());
                met += declared.met().size();
                unmet += declared.unmet().size();
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
                openIn.put(module.module() + "/declarations", declared.undecided().size());
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
                    undecided += account.undecided().size();
                    for (BorderObligationPointAssessment gap : account.unmet()) {
                        long found = findingsAbout(behavior, gap);
                        if (found != 1) {
                            wrong.add(reported.name() + " " + behavior.name() + ": a gap at "
                                    + gap.point() + " carries " + found + " findings");
                        }
                    }
                    openIn.put(module.module() + "/" + behavior.name(),
                            account.undecided().size());
                    for (BorderObligationPointAssessment open : account.undecided()) {
                        carriesNoFinding(wrong, reported.name(), open,
                                findingsAbout(behavior, open));
                    }
                }
            }
            saidUnderEachBlock(wrong, reported.name(), page, openIn);
        }

        String reached = "met " + met + ", unmet " + unmet + ", undecided " + undecided;
        assertEquals(List.of(), wrong, "an obligation the count holds is met, marked or named");
        assertTrue(met > 0 && unmet > 0 && undecided > 0, "every state is reached: " + reached);
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
     * As many `?` lines under each block as that block counted obligations nobody could decide.
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
                                           java.util.SequencedMap<String, Integer> undecided) {
        java.util.Map<String, Integer> said = new java.util.LinkedHashMap<>();
        undecided.keySet().forEach(block -> said.put(block, 0));
        String module = null;
        String block = null;
        for (String line : page.lines().toList()) {
            if (!line.isBlank() && !line.startsWith(" ")) {
                module = line.strip().split("\\s+")[0];
                block = null;
            } else if (line.startsWith("  ") && !line.startsWith("   ") && module != null) {
                String named = module + "/" + line.strip().split("\\s+")[0];
                block = undecided.containsKey(named) ? named : block;
            } else if (block != null
                    && line.strip().startsWith("? undecided whether a row is at")) {
                said.merge(block, 1, Integer::sum);
            }
        }
        undecided.forEach((where, owed) -> {
            if (!owed.equals(said.get(where))) {
                wrong.add(source + " " + where + ": " + owed + " obligations nobody could decide"
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

    /** One report and what to call the sources it is about. */
    private record Reported(String name, AdequacyReport report, SourceNameResolver names) {}

    private static List<Reported> reports() {
        List<Reported> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            out.add(new Reported(corpus.name(), analysed.report(), corpus.names()));
        }
        Compilation unread = Compilation.ofSource(TOO_LARGE_TO_OBSERVE, "Main");
        unread.measure(Adequacy.Asked.fullReport());
        unread.answerEverything();
        out.add(new Reported("example.unread", AdequacyReport.of(unread),
                SourceNameResolver.identity()));
        return out;
    }
}
