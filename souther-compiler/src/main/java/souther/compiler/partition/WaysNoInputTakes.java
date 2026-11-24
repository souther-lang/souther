package souther.compiler.partition;

import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * The ways one reading of a body proved no input takes, as it proves them
 * ({@link DecisionNaming#join}).
 *
 * <p>One register for the body, shared down every scope as the names of its conditions are: a way
 * proved closed under a binding is the same way outside it.
 */
final class WaysNoInputTakes {

    /** Each way once, by what it consulted and went through, with the first proof had of it and
     *  what the proof says the way is. */
    private final Map<DecisionPath.Way, DecisionReading.Excluded> proved = new LinkedHashMap<>();

    /**
     * What each way asked of comes to, by what it consulted: the ways a body is joined into, and
     * the ways a proof is had of as few conditions as still give it, ask about the same conditions
     * over and over, met in one order or another. What a way states is what each condition it
     * consulted states coming out as it did, which the reading of the body answers once.
     *
     * <p>Keyed by the way — the rule and the constructions it goes through — while the proof reads
     * what each condition and each construction states. The two are one question because a
     * condition states one thing however often a way consults it
     * ({@link DecisionPath.Consulted#again}), and so does a construction: two ways that are the
     * same rule through the same constructions state the same of the input. A condition whose
     * statement turned on where it was consulted would have to be a condition of its own, or this
     * would answer one way with another's proof.
     */
    private final Map<DecisionPath.Way, Asked> asked = new HashMap<>();

    /** The figure this reading takes conditions in up to, in all, as it stands for the compilation
     *  reading the body ({@link CompositionBudget#CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE}). */
    private final Figure.Budget figure =
            CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE.reached();

    /** How many more conditions this reading takes in, in all. */
    private int takenInLeft = figure.at();

    /** How many times a walk asked to take a condition in and was told no. */
    private int refused;

    /**
     * What asking whether some input takes a way came to: three answers, because a walk that was
     * told no to a condition it asked to take in proves nothing and has not shown that some input
     * takes the way either.
     */
    sealed interface Asked {

        /** No input takes the way, for {@code why}. */
        record Proved(NoInputTakesIt why) implements Asked {

            public Proved {
                Objects.requireNonNull(why, "a proof says what it was had from");
            }
        }

        /** The walk was had in full and proved nothing: the way is kept. */
        record NotProved() implements Asked {}

        /** The figure was spent before or during the walk, so what the way comes to is not known:
         *  the way is kept, and a reader told why. */
        record StoppedAt(Figure figure) implements Asked {

            public StoppedAt {
                Objects.requireNonNull(figure, "a walk stopped at some figure");
            }
        }

        /** The proof, where there is one. */
        default Optional<NoInputTakesIt> proof() {
            return this instanceof Proved(NoInputTakesIt why) ? Optional.of(why) : Optional.empty();
        }
    }

    /**
     * What asking whether some input takes {@code consulted} comes to, asked once for what it
     * consulted, where {@code proving} is the walk that answers it: nothing taken in once this
     * reading has taken in as many conditions as it does in all, which is no proof and keeps the
     * way.
     */
    Asked whyNoInputTakes(DecisionPath.Way consulted, Supplier<Optional<NoInputTakesIt>> proving) {
        Asked known = asked.get(consulted);
        if (known != null) {
            return known;
        }
        if (takenInLeft == 0) {
            return new Asked.StoppedAt(figure);
        }
        int refusedBefore = refused;
        Optional<NoInputTakesIt> answered = proving.get();
        Asked out = answered.<Asked>map(Asked.Proved::new).orElseGet(() ->
                refused > refusedBefore ? new Asked.StoppedAt(figure) : new Asked.NotProved());
        asked.put(consulted, out);
        return out;
    }

    /**
     * Whether a proof may take one more condition in, counting it if so. A walk told no takes the
     * condition in as nothing, which narrows nothing and so proves nothing past it, and what it
     * comes to is said to have stopped at the figure.
     */
    boolean takesIn() {
        if (takenInLeft == 0) {
            refused++;
            return false;
        }
        takenInLeft--;
        return true;
    }

    /** That no input takes the way {@code excluded} is, getting past every construction on it,
     *  and what the proof says the way is. */
    void add(DecisionPath path, DecisionReading.Excluded excluded) {
        proved.putIfAbsent(path.way(), excluded);
    }

    /**
     * The ways proved, none of which another stands for. A way that consulted everything another
     * did and more is a way past that one, and its rules are the other's already. Two ways neither
     * of which stands for the other may still both stand for some rule — two proofs had of
     * different conditions — and each is a proof of its own, so both are said.
     */
    List<DecisionReading.Excluded> leastOfThem() {
        List<DecisionReading.Excluded> out = new ArrayList<>();
        for (DecisionReading.Excluded each : proved.values()) {
            boolean pastAnother = proved.values().stream().anyMatch(other -> other != each
                    && other.standsFor(each.way()));
            if (!pastAnother) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }
}
