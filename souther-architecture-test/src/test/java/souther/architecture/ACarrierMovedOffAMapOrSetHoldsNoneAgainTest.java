package souther.architecture;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * A carrier moved off {@code java.util.Map} and {@code java.util.Set} does not hold one again.
 *
 * <p>Each carrier below holds a {@link souther.compiler.carrier.Lookup}, a
 * {@link souther.compiler.carrier.Membership} or {@link souther.compiler.observe.ElementsTaken} where
 * it held a map or a set. Those answer what a key is bound to, or whether something is in, and offer
 * no {@code keySet}, {@code entrySet}, {@code iterator} or {@code forEach} to take an order off. A map
 * or a set offers all of them, and one built by copying another salts the order they hand back —
 * differently on some runs than on others. A reader that reached for such a walk does not compile
 * against the carrier's type, so the type is what stops that reader. What a type cannot stop is the
 * declaration going back the other way: an edit giving the field a map again would compile, so the
 * field is read back and refused if it does ({@link MapOrSetFields}).
 *
 * <p>The carriers are named one by one because they were moved one by one. A rule over every field
 * {@code souther.compiler.partition} declares would answer about the fields still to move as much as
 * about these, and would be red for reasons that have nothing to do with a regression. Once the whole
 * package is moved, every field it declares is something the compiled output can be asked for
 * directly ({@link CompiledOutputs#inTheClassesOf}), and a rule built that way replaces this list.
 * Until then, a carrier moved on its own is added here. A nested class is named as its class file
 * names it, with a {@code $} between it and what it is nested in.
 */
class ACarrierMovedOffAMapOrSetHoldsNoneAgainTest {

    @ParameterizedTest
    @ValueSource(strings = {
            // pins: what a key is bound to, asked by key.
            "souther/compiler/partition/Interpretation",
            // The behaviors this one depends on, asked whether a behavior is one of them.
            "souther/compiler/partition/DecisionSubjects",
            // Which class a row is in at one position.
            "souther/compiler/partition/Generator$ObservedRow",
            // The value a module states at each parameter; whether there are any is the origin's
            // to say.
            "souther/compiler/partition/Generator$Baseline",
            // What the walk collected at each comparison, asked by comparison.
            "souther/compiler/partition/ReachingCuts",
            // The elements a class was reached through, the same value a row's occurrences hold.
            "souther/compiler/observe/Classification$At",
            // The elements an occurrence was reached through, outermost first: the readings of a
            // row are built and cut at a bound from that order.
            "souther/compiler/partition/BehaviorInputs$Occurrence"})
    void noFieldOfTheCarrierIsAMapOrASet(String carrier) {
        MapOrSetFields.assertHoldsNone(CompiledOutputs.ofWhatThisRepositoryPublishes(), carrier);
    }
}
