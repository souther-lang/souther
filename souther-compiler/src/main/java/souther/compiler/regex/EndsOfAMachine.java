package souther.compiler.regex;

import java.util.Collections;
import java.util.Map;
import java.util.Optional;
import java.util.WeakHashMap;
import java.util.concurrent.ConcurrentHashMap;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * Where the numbers of the strings one machine accepts lie at their ends — how many code points a
 * string is, what they come to, and the code point at each index — worked out once a machine.
 *
 * <p>Each is a function of the machine and of nothing else, and a reader asks it of every region
 * a search narrows: a walk that tries a value of one number asks again where every other number of
 * the same strings lies. Worked out each time, each asking walks the machine again.
 *
 * <p>Held beside the machine and not on {@link Language}, for the reason
 * {@link StringsHeldAsWritten} is: a language is carried under a great many answers, and a field
 * on it would put one more object that compares by address under every one of them. Keyed by the
 * machine itself, which compares by address, and held weakly so that an entry goes with its
 * machine. Two threads that ask first work out two equal values and keep one.
 */
final class EndsOfAMachine {

    private static final Map<Automaton, EndsOfAMachine> HELD =
            Collections.synchronizedMap(new WeakHashMap<>());

    private final Automaton machine;
    private volatile Optional<Language.Ends> lengths;
    private volatile Optional<Language.Ends> sums;
    private final Map<Integer, Optional<Language.Ends>> atIndex = new ConcurrentHashMap<>();

    private EndsOfAMachine(Automaton machine) {
        this.machine = machine;
    }

    /** The ends of {@code machine}'s strings, a {@link Language}'s canonical machine. */
    static EndsOfAMachine of(Automaton machine) {
        EndsOfAMachine had = HELD.get(machine);
        if (had == null) {
            had = new EndsOfAMachine(machine);
            EndsOfAMachine raced = HELD.putIfAbsent(machine, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }

    /** {@link Language#lengths}. */
    Language.Ends lengths() {
        Optional<Language.Ends> held = lengths;
        if (held == null) {
            held = Optional.ofNullable(CodePointSums.range(machine, _ -> 1, _ -> 1));
            lengths = held;
        }
        return held.orElse(null);
    }

    /** {@link Language#sumsOfCodePoints}. */
    Language.Ends sumsOfCodePoints() {
        Optional<Language.Ends> held = sums;
        if (held == null) {
            held = Optional.ofNullable(CodePointSums.range(machine, CodePoints::least,
                    over -> over.ranges().getLast().to()));
            sums = held;
        }
        return held.orElse(null);
    }

    /** {@link Language#codePointsAt(int)}. */
    Language.Ends codePointsAt(int index) {
        return atIndex.computeIfAbsent(index,
                at -> Optional.ofNullable(CodePointSums.atIndex(machine, at))).orElse(null);
    }
}
