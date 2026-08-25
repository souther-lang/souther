package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.CheckedEnsures;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Contract;
import souther.compiler.execute.ExampleExecution;

import java.util.List;
import java.util.Map;

/**
 * What an evaluation of one module's examples reads, put together in one place.
 *
 * <p>Four readers wanted the same thing and each worked it out again: running a source's rows,
 * building the fakes it wrote, comparing what two written statements say, and handing the rows to a
 * caller that runs them one at a time. The same six questions asked of the same module, and the
 * same lines deciding whether the answers were there yet, written four times.
 *
 * <p>What that cost is not the repetition. It is that "this module can have its examples evaluated"
 * had four definitions and nothing said they were the same one — a reader added later got whichever
 * of them it was copied from, and a condition tightened in one place stayed loose in the other
 * three. Asked here, there is one.
 *
 * <p><b>Not a key, and it must not become one.</b> What this hands back is not a value: a
 * {@code Symbols} closes over the store it resolves against, so an answer holding one would be tied
 * to the session it was taken from and could never equal its own recomputation — which is the one
 * thing this store's answers may not do. It is why the symbols are reached through a helper rather
 * than a key of their own. Each of the six parts is memoised where it is answered; putting them
 * side by side is the cheap part and is done afresh.
 *
 * <p>Null where any part of it is missing, and it does not say which. What a caller does about a
 * module that cannot be read yet differs — one goes absent, one has nothing to report, one raises —
 * and each of those is the caller's answer to its own question rather than a shade of this one.
 */
public final class ExampleExecutions {

    private ExampleExecutions() {}

    /** The environment {@code module}'s examples are evaluated in, or null where this compile has
     *  not settled it. */
    public static ExampleExecution of(Db db, String module) {
        Answer<Prepared> prepared = db.ask(new Shapes.Prepared(module));
        Answer<Symbols> scope = Names.derivedSymbols(db, module);
        Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(module));
        if (!prepared.present() || !scope.present() || !sigs.present()) {
            return null;
        }
        if (!db.ask(new Bodies.Checked(module)).present()) {
            return null;   // a module that did not check has nothing to run
        }
        // Asked for as a readiness condition rather than as an input to reading them: a module
        // whose requirements are not settled is not one to read statements off yet.
        Map<String, List<BehaviorRequirement>> requirements =
                db.ask(new Bodies.Requirements(module)).value();
        Map<String, CheckedEnsures> declared = db.ask(new Bodies.Contracts(module)).value();
        if (requirements == null || declared == null) {
            return null;
        }
        // The reading that runs. What decides a row is the emitted check (spec §example-ensures),
        // and this is what that check was emitted from.
        Map<String, Contract> contracts = CheckedEnsures.executable(declared);
        // The one part that may be empty rather than missing. A module defining no value of its own
        // reaches none by name, which is a module rather than an unanswered question.
        Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(module)).value();
        return new ExampleExecution(prepared.value(), scope.value(), sigs.value(),
                requirements, values == null ? Map.of() : values, contracts,
                Output.deadlineOf(db), Output.policyOf(db));
    }
}
