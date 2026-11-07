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
 * machine.
 *
 * <p>What is held is the ends and nothing else, and never the machine: an entry is let go only
 * once nothing holds its key strongly, and the entry's own value holding it would be something
 * that does. So the machine is handed in by whoever asks, as it is by the language it is the
 * machine of. Two threads that ask first work out two equal values and keep one.
 */
final class EndsOfAMachine {

    private static final Map<Automaton, EndsOfAMachine> HELD =
            Collections.synchronizedMap(new WeakHashMap<>());

    private volatile Optional<Language.Ends> lengths;
    private volatile Optional<Language.Ends> sums;
    private final Map<Integer, Optional<Language.Ends>> atIndex = new ConcurrentHashMap<>();

    private EndsOfAMachine() {
    }

    /** {@link Language#lengths} of {@code machine}, a {@link Language}'s canonical machine. */
    static Language.Ends lengths(Automaton machine) {
        EndsOfAMachine held = heldFor(machine);
        Optional<Language.Ends> worked = held.lengths;
        if (worked == null) {
            worked = Optional.ofNullable(CodePointSums.range(machine, _ -> 1, _ -> 1));
            held.lengths = worked;
        }
        return worked.orElse(null);
    }

    /** {@link Language#sumsOfCodePoints} of {@code machine}. */
    static Language.Ends sumsOfCodePoints(Automaton machine) {
        EndsOfAMachine held = heldFor(machine);
        Optional<Language.Ends> worked = held.sums;
        if (worked == null) {
            worked = Optional.ofNullable(CodePointSums.range(machine, CodePoints::least,
                    over -> over.ranges().getLast().to()));
            held.sums = worked;
        }
        return worked.orElse(null);
    }

    /** {@link Language#codePointsAt(int)} of {@code machine}. */
    static Language.Ends codePointsAt(Automaton machine, int index) {
        return heldFor(machine).atIndex.computeIfAbsent(index,
                at -> Optional.ofNullable(CodePointSums.atIndex(machine, at))).orElse(null);
    }

    private static EndsOfAMachine heldFor(Automaton machine) {
        EndsOfAMachine had = HELD.get(machine);
        if (had == null) {
            had = new EndsOfAMachine();
            EndsOfAMachine raced = HELD.putIfAbsent(machine, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }
}
