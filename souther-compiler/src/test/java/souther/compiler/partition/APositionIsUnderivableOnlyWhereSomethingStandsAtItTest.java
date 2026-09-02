package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.diag.Located;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A position comes back underivable exactly where something at it is still standing.
 *
 * <p>Two ways for that to be so, and no third. The reading did not reach into what the position
 * holds, so nothing was read there at all; or a question the rules of the position raise is one
 * nothing answered. Both are facts kept where they are made — the first by the structural reading,
 * the second by the accounting that holds every question a rule raises against whatever answered
 * it — and a verdict that says this compiler could not read a position is a projection of them.
 *
 * <p><b>Neither direction is the interesting one on its own.</b> A verdict said over a position
 * whose questions were all answered sends a reader after a limit that is not there; a position with
 * a question standing and any other verdict says the model was read in full when it was not. So the
 * contract is the biconditional, and a reading that satisfied it by refusing to say anything would
 * have to fail the other half.
 *
 * <p>What this does not read is the findings a report is written from. A verdict recovered from
 * what happens to have been published, or a publication recovered from a verdict, is the
 * reconstruction the accounting exists to take away — so the population here is the positions
 * themselves and the two accounts that answer for them.
 */
class APositionIsUnderivableOnlyWhereSomethingStandsAtItTest {

    /**
     * A rule about a pair of positions, which each of them is read through and neither divided by.
     *
     * <p>Written as a record of two fields because that is the one shape where a rule of the model
     * names two positions of one input.
     */
    private static final String A_RULE_ABOUT_A_PAIR = """
            module probe

            data Ok

            data Span = { from: Int, to: Int }
                invariant ordered = from <= to

            behavior read : (s: Span) -> Ok
            let read (s) = Ok
            """;

    /** A rule that divides the position into the strings it accepts and the rest. */
    private static final String A_RULE_NO_ORDER_HOLDS = """
            module probe

            data Ok

            data Code = String
                invariant format = String.matches("T[0-9]{3}", value)

            behavior read : (c: Code) -> Ok
            let read (c) = Ok
            """;

    /** A rule about a number the position cancels out of, which places nothing on it. */
    private static final String A_RULE_THAT_CUTS_NOTHING = """
            module probe

            data Ok

            data N = Int
                invariant nothing = value - value > 0

            behavior read : (n: N) -> Ok
            let read (n) = Ok
            """;

    /** Nothing written about the position at all. */
    private static final String NOTHING_WRITTEN = """
            module probe

            data Ok

            data Plain = { a: Int, b: String }

            behavior read : (p: Plain) -> Ok
            let read (p) = Ok
            """;

    private static final List<String> MODELS = List.of(A_RULE_ABOUT_A_PAIR, A_RULE_NO_ORDER_HOLDS,
            A_RULE_THAT_CUTS_NOTHING, NOTHING_WRITTEN);

    /** The models this compiler is written against, which is where the shapes an author writes are. */
    @Test
    void everyCorpusPositionAgrees() {
        List<String> disagreeing = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            disagreeing.addAll(disagreeingIn(corpus.analyse().compilation()));
        }
        assertEquals(List.of(), disagreeing,
                "a verdict and what is standing at the position say different things");
    }

    /** And the shapes above, each of which a corpus need not hold. */
    @Test
    void everyPositionOfTheseModelsAgrees() {
        List<String> disagreeing = new ArrayList<>();
        for (String model : MODELS) {
            disagreeing.addAll(disagreeingIn(analysed(model)));
        }
        assertEquals(List.of(), disagreeing,
                "a verdict and what is standing at the position say different things");
    }

    /**
     * And where nothing stands, which of the other two it is turns on whether a rule is filed here.
     *
     * <p>The half the contract above does not reach. A position everything was answered about is
     * one of two things, and they are as far apart as the verdicts get: the model states something
     * here that came to no line, or it states nothing at all. Read from the findings the rules
     * produced rather than from what the verdict was built out of, so that the two are not one
     * answer written twice.
     */
    @Test
    void whereNothingStandsTheVerdictFollowsTheRulesFiledAtThePosition() {
        List<String> disagreeing = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            disagreeing.addAll(misclassifiedIn(corpus.analyse().compilation()));
        }
        for (String model : MODELS) {
            disagreeing.addAll(misclassifiedIn(analysed(model)));
        }
        assertEquals(List.of(), disagreeing,
                "a verdict and the rules filed at the position say different things");
    }

    /**
     * And the population is one the contract can be broken in, which a count of nothing is not.
     *
     * <p>Both halves have to be reachable here or the two above pass by having nothing to say: a
     * position no class came back for, and one that came back underivable.
     */
    @Test
    void thePopulationHoldsPositionsOfBothKinds() {
        List<UndividedPosition> undivided = new ArrayList<>();
        for (String model : MODELS) {
            undivided.addAll(undividedIn(analysed(model)));
        }
        assertFalse(undivided.isEmpty(), "no position came back without a class");
        assertFalse(undivided.stream().noneMatch(
                        each -> each.why() instanceof UndividedPosition.Why.CannotDerive),
                () -> "no position came back underivable: " + undivided);
    }

    /** Where a verdict and the accounts that answer for the position do not say the same thing. */
    private static List<String> disagreeingIn(Compilation compilation) {
        List<String> out = new ArrayList<>();
        forEachBehavior(compilation, (behavior, divided) -> {
            Set<TermPath> standing = new LinkedHashSet<>();
            for (StandingQuestion question : divided.unanswered()) {
                standing.add(question.asks().path());
            }
            Set<TermPath> unreached = new LinkedHashSet<>();
            for (PositionAccount at : divided.positions()) {
                if (at.notReachedInto() != null) {
                    unreached.add(at.path());
                }
            }
            // And a rule filed at the position that a reading did not get through. Such a rule
            // raises no question a caller can be told about where a body wrote it — a comparison
            // raises and answers in one breath — so the accounting has nothing to say and the
            // finding the reader made is what says it.
            Set<TermPath> stopped = new LinkedHashSet<>();
            for (RuleWithoutALine rule : divided.rulesWithoutALine()) {
                if (rule.why() instanceof BlockReason.RuleReadingStopped) {
                    stopped.add(rule.at().path());
                }
            }
            for (UndividedPosition each : divided.undivided()) {
                boolean underivable = each.why() instanceof UndividedPosition.Why.CannotDerive;
                boolean somethingStands = standing.contains(each.at())
                        || unreached.contains(each.at()) || stopped.contains(each.at());
                if (underivable != somethingStands) {
                    out.add(behavior + " at " + each.at() + ": " + each.why()
                            + (somethingStands ? " with something standing at it"
                                    : " with every question at it answered and the position read"));
                }
            }
        });
        return out;
    }

    /**
     * Where a position everything was answered about is one of the other two and the rules filed at
     * it say the other.
     */
    private static List<String> misclassifiedIn(Compilation compilation) {
        List<String> out = new ArrayList<>();
        forEachBehavior(compilation, (behavior, divided) -> {
            Set<TermPath> stated = new LinkedHashSet<>();
            for (RuleWithoutALine rule : divided.rulesWithoutALine()) {
                // Read from the end to the end, which is the model stating something. A rule a
                // reading did not get through states nothing anybody here can act on, and counting
                // it would be this check making the assumption the production code makes.
                if (rule.why() instanceof BlockReason.ReadToEndWithoutLine) {
                    stated.add(rule.at().path());
                }
            }
            for (UndividedPosition each : divided.undivided()) {
                if (each.why() instanceof UndividedPosition.Why.CannotDerive) {
                    continue;
                }
                boolean statesSomething = stated.contains(each.at());
                boolean saidToState =
                        each.why() instanceof UndividedPosition.Why.StatedWithoutALine;
                if (statesSomething != saidToState) {
                    out.add(behavior + " at " + each.at() + ": " + each.why()
                            + (statesSomething ? " with a rule filed at it"
                                    : " with no rule filed at it"));
                }
            }
        });
        return out;
    }

    private static List<UndividedPosition> undividedIn(Compilation compilation) {
        List<UndividedPosition> out = new ArrayList<>();
        forEachBehavior(compilation, (behavior, divided) -> out.addAll(divided.undivided()));
        return out;
    }

    private static void forEachBehavior(Compilation compilation,
                                        java.util.function.BiConsumer<String,
                                                Partitions.Partitioning> read) {
        for (String module : compilation.modules()) {
            Answer<Prepared> prepared = compilation.db().ask(new Shapes.Prepared(module));
            if (!prepared.present()) {
                continue;
            }
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;
                }
                Answer<Partitions.Partitioning> divided =
                        compilation.db().ask(new Adequacy.Divided(module, spec.name()));
                if (divided.present()) {
                    read.accept(module + "." + spec.name(), divided.value());
                }
            }
        }
    }

    private static Compilation analysed(String source) {
        List<Located> warnings = new ArrayList<>();
        return Compiler.analyzedModules(List.of(source), ModulePath.EMPTY, warnings,
                Adequacy.Asked.fullReport());
    }
}
