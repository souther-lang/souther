package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Set;

/**
 * What is being done about a behavior's {@code ensures}, answered once for the whole compilation.
 *
 * <p>One value rather than a pair of questions. Asked as "does the callee check" and "does a
 * crossing check", the two are complements in arithmetic and independent in the program: four
 * combinations can be written where three answers exist, and the two that should be unreachable are
 * the ones that matter. Both false is a clause nothing checks, which is the failure this whole
 * mechanism exists to prevent and which nothing would report. Both true is a clause checked twice,
 * which is silent and costs a run on every call. They would be read at the same place, too — a
 * pipeline stage's application is where a bodied stage's own check already runs and where an
 * injected stage's crossing check goes.
 *
 * <p>Four cases and not three, because "there is no check" and "this stage did not decide" are not
 * the same answer. The first is a conclusion, reached by reading what a behavior declared. The
 * second is the absence of one, and it is what a compilation has to say about a behavior another
 * module declared. Collapsed into one variant they read alike at every use, and the thing that is
 * waiting to be designed reads as a fact somebody measured.
 */
public sealed interface EnsuresEnforcement {

    /**
     * The module that declares the behavior checks it where the behavior answers.
     *
     * <p>Its body is here, so this is the one place every application goes through — a Souther
     * caller, a Java caller, a pipeline stage — and a caller emits nothing.
     */
    record AtTheCallee(BehaviorContract contract) implements EnsuresEnforcement {

        public AtTheCallee {
            if (contract == null) {
                throw new IllegalArgumentException("a check is of something a behavior declared");
            }
        }
    }

    /**
     * The answer arrives from outside, so every crossing into generated code checks it.
     *
     * <p>An injected behavior's {@code apply} is supplied by the Java implementation (ADR-0056), so
     * there is no body here to check in. The line is the one the Decoder draws for an outside value:
     * where an answer enters the domain.
     *
     * <p>This says where a check goes, not how many go anywhere. A behavior only the application's
     * own Java calls has no crossing in this compilation and gets no check emitted — a count of
     * crossings, and not an answer of its own.
     */
    record AtEachCrossing(BehaviorContract contract) implements EnsuresEnforcement {

        public AtEachCrossing {
            if (contract == null) {
                throw new IllegalArgumentException("a check is of something a behavior declared");
            }
        }
    }

    /** The behavior declares no clause, so there is nothing to run. A conclusion, reached by reading
     *  what the behavior declared. */
    record NoContract() implements EnsuresEnforcement {

        /** The one of these there is. It holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final NoContract INSTANCE = new NoContract();
    }

    /**
     * This compilation has not decided, which is its answer for a behavior another module declared.
     *
     * <p>Not {@link NoContract}. Such a behavior may well declare a clause — the artifact carries the
     * declaration and this compilation can read it — and what is missing is not the clause but the
     * basis for acting on it: which boundary revision the artifact was published under, whether what
     * it published is an executable guarantee at all, and on what basis this compilation may rely on
     * it. Those make an ownership model, and answering them by reading a module name would decide
     * them by a spelling.
     *
     * <p>So this is where the unfinished thing is, said as one answer. A behavior that reaches here
     * is one whose clause nothing in this compilation runs, and that is visible rather than arrived
     * at: the day cross-module ownership is designed, this answer becomes one of the two above, and
     * the sites that read it are the sites that already had to say what they do with it.
     */
    record NotDecidedHere() implements EnsuresEnforcement {

        /** The one of these there is, for the same reason {@link NoContract#INSTANCE} is. */
        public static final NotDecidedHere INSTANCE = new NotDecidedHere();
    }

    /**
     * What is checked, or null where nothing is and where nothing was decided.
     *
     * <p>The contract rides the answer rather than being looked up beside it. An emitter needs both
     * — where the check goes and what it says — and handed them apart it would hold a case saying
     * there is a check to emit next to a table with nothing under that name, or a contract for a
     * behavior the answer said states nothing.
     */
    default BehaviorContract contract() {
        return switch (this) {
            case AtTheCallee(BehaviorContract c) -> c;
            case AtEachCrossing(BehaviorContract c) -> c;
            case NoContract ignored -> null;
            case NotDecidedHere ignored -> null;
        };
    }

    /**
     * What {@code decided} says about {@code behavior}, and {@link NotDecidedHere} where it says
     * nothing.
     *
     * <p>The one place a miss is read. A table of this compilation's decisions holds one for every
     * behavior this compilation declares, so a name it has nothing under is a name from somewhere
     * else — and answering that with {@link NoContract} would be this table reporting, about a
     * declaration it never read, the conclusion it reaches for declarations it did.
     */
    static EnsuresEnforcement in(Map<ValueName.Behavior, EnsuresEnforcement> decided,
                                 ValueName.Behavior behavior) {
        EnsuresEnforcement answered = decided.get(behavior);
        return answered == null ? NotDecidedHere.INSTANCE : answered;
    }

    /**
     * What is being done about {@code behavior}'s clause, read from what it declares and from
     * whether its body comes from outside.
     *
     * <p>The one place the two facts meet, and it is asked only of a behavior this compilation
     * declares. {@code injected} has to be the set as the requirements pass answered it: the backend
     * goes on adding to a set of that name, so that a behavior this module gives a body to but
     * reaches as a dependency joins it, and a reader arriving afterwards would find a bodied
     * behavior sitting among the injected ones.
     */
    static EnsuresEnforcement of(ValueName.Behavior behavior,
                                 Map<String, BehaviorContract> contracts,
                                 Set<ValueName.Behavior> injected) {
        BehaviorContract contract = contracts.get(behavior.name());
        if (contract == null) {
            return NoContract.INSTANCE;
        }
        return injected.contains(behavior)
                ? new AtEachCrossing(contract)
                : new AtTheCallee(contract);
    }
}
