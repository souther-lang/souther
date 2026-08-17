package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Set;

/**
 * Where a behavior's {@code ensures} is checked, answered once for the whole compilation.
 *
 * <p>Three answers, and they are one value rather than two questions. Asked as a pair of
 * predicates — "does the callee check" and "does a crossing check" — the two are complements in
 * arithmetic and independent in the program: four combinations can be written where three states
 * exist, and the two that should not be reachable are the two that matter. Both false is a clause
 * nothing checks, which is the failure this whole mechanism exists to prevent and which nothing
 * would report. Both true is a clause checked twice, which is silent and costs a run.
 *
 * <p>They would be read at the same place, too. A pipeline stage's application is where a bodied
 * stage's own check is already running and where an injected stage's crossing check goes, so the
 * site most likely to double up is the site that would read both predicates.
 *
 * <p>Read from here, the site asks one value and acts on the case it got. There is no combination to
 * be told is impossible by something outside the code.
 */
public sealed interface WhereTheCheckIs {

    /**
     * The module that declares the behavior emits the check where the behavior answers.
     *
     * <p>Its body is here, so this is the one place every application goes through — a Souther
     * caller, a Java caller, a pipeline stage — and a caller emits nothing.
     */
    record AtTheCallee(BehaviorContract contract) implements WhereTheCheckIs {

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
     * own Java calls has no crossing in this compilation and gets no check emitted — which is a
     * count of crossings and not a fourth state, and is why a compilation emitting none of them is
     * not something to read back as an answer of its own.
     */
    record AtEachCrossing(BehaviorContract contract) implements WhereTheCheckIs {

        public AtEachCrossing {
            if (contract == null) {
                throw new IllegalArgumentException("a check is of something a behavior declared");
            }
        }
    }

    /**
     * There is no executable contract: the behavior declares no clause.
     *
     * <p>What this is not: a behavior that declares one and happens to have nothing to check here.
     * A clause always has somewhere it is checked — the two above are those places — so the only way
     * to reach this is by there being no clause. Should a clause ever be declared and deliberately
     * left unchecked, that is a fourth answer and is written as one, because a reader acting on this
     * one is acting on "the model stated nothing".
     */
    record Nowhere() implements WhereTheCheckIs {

        /** The one of these there is. It holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final Nowhere INSTANCE = new Nowhere();
    }

    /**
     * What is checked, or null where nothing is.
     *
     * <p>The contract rides the answer rather than being looked up beside it. An emitter needs both
     * — where the check goes and what it says — and handed them apart it would hold a case saying
     * there is a check to emit next to a table with nothing under that name, or a contract for a
     * behavior the answer said states nothing. Neither is writable here: the two cases that have
     * somewhere to put a check are the two that carry one.
     */
    default BehaviorContract contract() {
        return switch (this) {
            case AtTheCallee(BehaviorContract c) -> c;
            case AtEachCrossing(BehaviorContract c) -> c;
            case Nowhere ignored -> null;
        };
    }

    /**
     * Where {@code behavior}'s check is, read from what it declares and from whether its body comes
     * from outside.
     *
     * <p>The one place the two facts meet. {@code injected} is the set of behaviors whose {@code
     * apply} a Java implementation supplies, and it has to be the set as the requirements pass
     * answered it: the backend goes on adding to a set of that name, so that a behavior this module
     * gives a body to but reaches as a dependency joins it, and a reader arriving afterwards would
     * find a bodied behavior sitting among the injected ones. Answered here, from the set before
     * anything else is put in it, there is one reading of it and nowhere for a second to disagree.
     */
    static WhereTheCheckIs of(ValueName.Behavior behavior,
                              Map<String, BehaviorContract> contracts,
                              Set<ValueName.Behavior> injected) {
        BehaviorContract contract = contracts.get(behavior.name());
        if (contract == null) {
            return Nowhere.INSTANCE;
        }
        return injected.contains(behavior)
                ? new AtEachCrossing(contract)
                : new AtTheCallee(contract);
    }
}
