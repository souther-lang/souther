package souther.compiler.execute;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.source.SourceId;

import java.util.List;
import java.util.Map;

/**
 * Everything an evaluation of one module's examples reads, as this compile settled it.
 *
 * <p>Not a second model of a module. What an output reads of a checked program is Core, lowered,
 * and an example is not there: a row's inputs and its expected value are expressions the checker
 * read and never lowered, and the definitions a fixture reaches are the ones a call expands rather
 * than the ones the module emits. So this is not the checked program under another name — it is the
 * stage the checked program does not have, and nothing here is a second answer to a question the
 * checked program already answers.
 *
 * <p>It carries and does not decide. Every part of it is some other question's answer, taken whole:
 * what the names mean, what each behavior's shape is, what it needs supplied, what the module
 * defines, and what its behaviors declare of what they answer. Nothing here re-derives one of those
 * from the others — a carrier that started answering would be the second model this is not.
 *
 * <p>What it does hold together is the correlation. The rows and the module they are rows of come
 * from one preparation and cannot be paired wrongly, which is the condition a run of them is
 * correct under; and the terms the rows are held to are this compile's, read once, so two runs of
 * one module are not two budgets.
 *
 * <p>Module-wide, with the source asked for at the question. Which file a row is written in decides
 * which rows a question is about, not what the module means, and a copy of this per source would
 * make "all of them" and "one file's" two states of one type.
 */
public final class ExampleExecution {

    private final Prepared prepared;
    private final Symbols symbols;
    private final Map<String, Sig> signatures;
    private final Map<String, List<BehaviorRequirement>> requirements;
    private final Map<String, Hir.FnDef> definitions;
    private final Map<String, BehaviorContract> contracts;
    private final Deadline deadline;
    private final EvaluationPolicy policy;

    public ExampleExecution(Prepared prepared, Symbols symbols, Map<String, Sig> signatures,
                            Map<String, List<BehaviorRequirement>> requirements,
                            Map<String, Hir.FnDef> definitions,
                            Map<String, BehaviorContract> contracts,
                            Deadline deadline, EvaluationPolicy policy) {
        this.prepared = prepared;
        this.symbols = symbols;
        // Taken as they are and not copied. Each is another question's settled answer, and this is
        // put together afresh every time it is asked for — it cannot be memoised, because a
        // `Symbols` closes over the store it resolves against — so copying four maps here would be
        // a cost paid on every reading to defend against a caller that does not exist.
        this.signatures = signatures;
        this.requirements = requirements;
        this.definitions = definitions;
        this.contracts = contracts;
        this.deadline = deadline;
        this.policy = policy;
    }

    /** What the module is called. */
    public String module() {
        return prepared.name();
    }

    /** Every row the module has, from its own file and from every file naming it. */
    public Prepared.Examples rows() {
        return prepared.forExamples();
    }

    /** The rows written in one source, projected the way the preparation projects them. */
    public Prepared.Examples rowsWrittenIn(SourceId source) {
        return prepared.forExamplesWrittenIn(source);
    }

    /** What a name written here means. */
    public Symbols symbols() {
        return symbols;
    }

    /** The shape of each of the module's behaviors. */
    public Map<String, Sig> signatures() {
        return signatures;
    }

    /** What each behavior needs supplied to it. */
    public Map<String, List<BehaviorRequirement>> requirements() {
        return requirements;
    }

    /** The definitions a row can reach by name, which is what a fixture applies. */
    public Map<String, Hir.FnDef> definitions() {
        return definitions;
    }

    /** What each behavior declares of what it answers, which is what holds a row's values to
     *  something. */
    public Map<String, BehaviorContract> contracts() {
        return contracts;
    }

    /** How long a reading may take before it is stopped. */
    public Deadline deadline() {
        return deadline;
    }

    /** What a run is counted against. */
    public EvaluationPolicy policy() {
        return policy;
    }
}
