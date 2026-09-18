package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatSourceWrote;
import souther.compiler.WhatSourceWrote.Carrier;
import souther.compiler.WhatWasCompiled;

import java.lang.classfile.ClassModel;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number and what some orders read do not travel as two things anybody can choose.
 *
 * <p>The rule beside {@link NothingTakesANumberAndAnotherNumbersOrdersTest}, one step along. There,
 * a term and a pair of orders may stand together as long as they are held to each other, and what
 * does the holding is {@link TermOrders#areOf}. Here the orders have been spent: {@code
 * WhatATermRead} is made on a pair of them and carries neither them nor the term, so what comes
 * back says which number it is an answer about nowhere at all. There is no {@code areOf} to call,
 * and a caller writing {@code termA} beside the answer read on {@code ordersOfB} is writing a
 * number the row does not hold at a position it does.
 *
 * <p>So the difference between the two rules is not what they sweep but what a witness is available
 * for. There, the two may be handed over together as long as something holds them to each other,
 * and a single place naming both — a map of the one to the other — is a thing whose entries can be
 * asked that question. Here nothing can be asked it, of a parameter or of what is inside a
 * container, so what this reports is the two meeting at all ({@link Carrier#meet}) and not only
 * their meeting in two places.
 *
 * <p><b>Both what is held and what is handed over.</b> A record component and a parameter give a
 * caller the same freedom, and the walk that reads a term on its orders and keeps the answer in a
 * local gives it none. What separates them is {@link WhatSourceWrote}, which is where a class file
 * is read.
 */
class NothingHoldsANumberBesideWhatSomeOrdersReadTest {

    /**
     * What a pair of orders read, which is an answer with no say left in which number it is of.
     *
     * <p>The kind and not the one name. An answer arrives as the arm it is — a number, a position
     * the row wrote nothing at — as readily as under the name they are all of, and each of those
     * says which number it is about exactly as little.
     */
    private static final List<String> READ = List.copyOf(
            WhatWasCompiled.everyKindOf("souther.compiler.partition.WhatATermRead"));

    /**
     * What names a number, taken from the rule beside this one and not widened.
     *
     * <p>{@code RealizationTarget} names one as plainly as a term does, so it gives a caller the
     * same freedom to put an answer under the wrong name. What is not here is anything that merely
     * has a term somewhere inside it: which values are derived from what is not something a class
     * file says, and a sweep that had to decide it would be a sweep nobody can read.
     */
    private static final List<String> TERM = Stream.of(
                    "souther.compiler.inputs.NumericTerm",
                    "souther.compiler.partition.RealizationTarget")
            .map(WhatWasCompiled::everyKindOf).flatMap(Set::stream).toList();

    @Test
    void nothingHoldsANumberBesideWhatSomeOrdersRead() {
        assertEquals(Set.of(), pairingsAmong(WhatSourceWrote::held),
                "what a pair of orders read says nothing about which number it is of, so a term"
                        + " held beside one is two things to get right and nothing that could hold"
                        + " them to each other; file the answers under the orders, which name their"
                        + " term");
    }

    @Test
    void nothingIsHandedANumberBesideWhatSomeOrdersRead() {
        assertEquals(Set.of(), pairingsAmong(WhatSourceWrote::handedOver),
                "handing the two over separately is where a caller chooses which term an answer is"
                        + " put under, and an answer read on one term's orders is no reading of"
                        + " another's");
    }

    /**
     * That both halves of the question are being read, so an empty answer means what it says.
     *
     * <p>Nothing pairs the two today, which is what a sweep that read nothing also reports. What
     * separates them is that each side is witnessed where it is known to be: places carrying a
     * number, and the reading that files its answers under the orders that read them — which names
     * what was read only inside what it is a map of, and so is seen only by reading through the
     * wrapping.
     */
    @Test
    void theScanReachesTheValuesThisRuleIsAbout() {
        Set<String> carryingANumber = new TreeSet<>();
        Set<String> holdingAReading = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            for (Carrier carrier : WhatSourceWrote.handedOver(model)) {
                if (carrier.sourceNames(TERM)) {
                    carryingANumber.add(carrier.where());
                }
            }
            for (Carrier carrier : WhatSourceWrote.held(model)) {
                if (carrier.names(READ)) {
                    holdingAReading.add(carrier.where());
                }
            }
        }

        int carrying = carryingANumber.size();
        assertTrue(carrying > 20,
                () -> "the sweep found only " + carrying + " places handed a number, which is not"
                        + " this compiler");
        assertTrue(holdingAReading.contains("souther.compiler.partition.QuantityReading"),
                () -> "the reading files its answers under the orders that read them and names what"
                        + " was read nowhere else, so a sweep that saw a type only where it is"
                        + " written bare would not have read it: " + holdingAReading);
    }

    private static Set<String> pairingsAmong(Carriers of) {
        Set<String> pairing = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            for (Carrier carrier : of.in(model)) {
                if (carrier.meet(TERM, READ)) {
                    pairing.add(carrier.where());
                }
            }
        }
        return pairing;
    }

    /** Which of the two places values stand a run is about. */
    private interface Carriers {
        List<Carrier> in(ClassModel model);
    }

}
