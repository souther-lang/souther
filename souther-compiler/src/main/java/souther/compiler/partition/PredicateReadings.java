package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StringPredicates;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

/**
 * One reading of the predicates a body applies to the strings at its positions.
 *
 * <p><b>Of the body the analysis reads</b> ({@link AnalysisBody}), which is the tree such a rule is
 * in. {@code String.startsWith(p, code)} is one of the language's own operations, and the tree a
 * backend emits has it expanded into the walk it turns into — read there, a body full of rules about
 * its strings holds none. So this takes the representation where the operation stands and reads it
 * as what it states.
 *
 * <p><b>Beside {@link ComparisonReadings} and not inside it.</b> The two read two trees, and what
 * each carries is where a rule stands in the tree it is in. One walk over both would be a reader of
 * two representations, and every question asked of it — where does this stand, which copy is it,
 * what is in force here — would first have to say which of the two it meant.
 *
 * <p><b>What a rule means and what it does to a position are still apart.</b> This says which
 * predicate was applied, which strings it states and what the subject is. Whether that restricts the
 * position or divides it turns on where the rule is written, and a rule in a body divides — so the
 * division is worked out where every rule reaching a position is held together, out of the sets this
 * left.
 *
 * <p><b>A rule nothing reads is no rule.</b> A predicate bound to a name the body never reads states
 * nothing about what the behavior answers, and a class divided off a position by it would be one no
 * value of the model is ever on either side of. So a reading is made only where what is computed is
 * read on the way to the answer, which is the one thing carried down this walk.
 */
record PredicateReadings(List<Reading> predicates) {

    PredicateReadings {
        predicates = List.copyOf(predicates);
    }

    /**
     * One predicate of the body, read where it is applied.
     *
     * @param origin which rule this is, which of the body's readings of it, and where a reader is
     *               sent to find it
     * @param stated the argument the rule is about and what the predicate states of it
     * @param reads  what the names in force here stand for, which is what resolves the subject to a
     *               position. It travels with the reading because it is not the same at every
     *               application: a predicate inside an expanded helper is about the argument the
     *               call handed it
     */
    record Reading(PredicateOrigin origin, StringPredicates.Stated stated, InputReads reads) {

        Reading {
            if (origin == null || stated == null || reads == null) {
                throw new IllegalArgumentException(
                        "a predicate that was read is some rule, read as something, somewhere");
            }
        }

        /** The argument the rule is about, for a caller that resolves it to a position. */
        Core subject() {
            return stated.subject();
        }

        /** What this compiler made of the strings the predicate states. */
        StringPredicates.Reading reading() {
            return stated.reading();
        }
    }

    /**
     * One reading of {@code body}.
     *
     * <p>Whose body it is is asked for, which is where this differs from the walk of comparisons.
     * There a reading is of a comparison the catalog named, and the name says whose body it stands
     * in; here there is no catalog and nothing else names the behavior, so a rule this finds could
     * be filed under no behavior at all.
     */
    static PredicateReadings of(String behavior, AnalysisBody body, InputReading read,
                                InputReads reads) {
        List<Reading> found = new ArrayList<>();
        walk(body.core(), behavior, read, reads, LiveFlow.of(body.core()), true, found);
        return new PredicateReadings(found);
    }

    /**
     * @param live whether what is computed here is read on the way to what the behavior answers
     *             with. Carried down because everything inside a value nothing reads is read by
     *             nothing either
     */
    private static void walk(Core e, String behavior, InputReading read, InputReads reads,
                             LiveFlow flow, boolean live, List<Reading> out) {
        Symbols symbols = read.symbols();
        if (live && e instanceof Core.PreservedCall call && call.origin().isWritten()) {
            // The text an author wrote is reached through the names in force here, which is what
            // this walk holds and the table does not. Handed a fold of its own, the table would
            // report a rule under `let prefix = "JP"` as one whose argument nothing worked out
            // while this walk had the answer.
            StringPredicates.Stated stated =
                    StringPredicates.statedBy(call, symbols, at -> reads.writtenStringOf(at, symbols));
            if (stated != null) {
                out.add(new Reading(
                        new PredicateOrigin(new RuleRef.Predicate(behavior, call.origin()),
                                new PredicateOccurrence(out.size()),
                                new RuleCitation.WrittenAt(Citation.of(call.pos()))),
                        stated, reads));
            }
        }
        switch (e) {
            // What a `let` computes is read on the way to the answer only where the name is read;
            // everywhere else a value stands in a body it is consumed by what it stands in. And its
            // body is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                walk(let.value(), behavior, read, reads, flow, live && flow.reads(let), out);
                walk(let.body(), behavior, read, reads.and(let.binder(), let.value()), flow, live,
                        out);
            }
            // And each arm under what the arm says the value it matched turned out to be. A name
            // the arm binds is the scrutinee's position narrowed to that case, so a predicate
            // written inside an arm is about a position the reading of the input has — read
            // without it, every rule an author writes inside a `match` was about nothing.
            case Core.Match match -> {
                walk(match.scrutinee(), behavior, read, reads, flow, live, out);
                for (Core.Case arm : match.cases()) {
                    walk(arm.body(), behavior, read, reads.insideArm(match, arm, symbols), flow,
                            live, out);
                }
            }
            default -> Core.forEachChild(e, child ->
                    walk(child, behavior, read, reads, flow, live, out));
        }
    }
}
