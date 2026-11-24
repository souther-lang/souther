package souther.compiler.regex;

import java.util.BitSet;
import java.util.function.Predicate;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * The states of a machine a walk may stop at from.
 *
 * <p>A canonical machine is complete: it steps over the code points it does not read into a state
 * that leads nowhere, and what a language reads is what leads to an end.
 */
final class LiveStates {

    private LiveStates() {}

    /** The states of {@code machine} from which some walk reaches a state it stops at. */
    static BitSet of(Automaton machine) {
        return of(machine, over -> !over.isEmpty());
    }

    /**
     * The states of {@code machine} from which some walk reaches a state it stops at, taking only
     * the steps over code points {@code crossed} says some of are ones to take.
     */
    static BitSet of(Automaton machine, Predicate<CodePoints> crossed) {
        BitSet live = new BitSet();
        for (int state = 0; state < machine.size(); state++) {
            live.set(state, machine.stopsAt(state));
        }
        boolean grew = true;
        while (grew) {
            grew = false;
            for (int state = 0; state < machine.size(); state++) {
                if (live.get(state)) {
                    continue;
                }
                for (Automaton.Step each : machine.stepsFrom(state)) {
                    if (live.get(each.to()) && crossed.test(each.over())) {
                        live.set(state);
                        grew = true;
                        break;
                    }
                }
            }
        }
        return live;
    }
}
