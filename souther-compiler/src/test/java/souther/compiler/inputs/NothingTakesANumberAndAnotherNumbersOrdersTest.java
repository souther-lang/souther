package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatSourceWrote;
import souther.compiler.WhatSourceWrote.Carrier;
import souther.compiler.WhatWasCompiled;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ClassDesc;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number and a pair of orders do not travel as two things anybody can choose.
 *
 * <p>{@link TermOrders} says which number it is of, so a reader that has one needs nothing else to
 * know what it is an answer about. What it does not stop by itself is a caller writing the number
 * down beside it: two arguments are two things to get right, and {@code f(termA, ordersOfB)}
 * compiles wherever the two are taken apart — which is the defect this reading exists to stop, said
 * one call along.
 *
 * <p>So the rule is about every place that takes both, whether it is a constructor, a factory or a
 * reader: either it does not take both, or it proves they agree. Proving is
 * {@link TermOrders#areOf}, and a method that takes both without calling it is what this reports.
 *
 * <p><b>Two places and not one.</b> A single thing naming both — a map of numbers to the orders
 * they are read on — is one thing to be handed, and whether what is inside it agrees is a question
 * about that thing. Such a map is how this compiler carries the two, and what keeps its entries
 * honest is asking {@code areOf} of each. What a caller can get wrong here is lining one value up
 * against another, which takes two places.
 *
 * <p><b>Two locals a closure took are not two places either.</b> The values a body closed over
 * arrive in a class file as a carrier because a closure needs one, and nobody chose either against
 * the other. What makes the meeting a choice is that one of the places was written.
 *
 * <p><b>Enumerated by the machine and not by a reader.</b> The three rounds of review this rule went
 * through each found another spelling of it — a record here, a signature there, a package-private
 * entry that came in with a refactor — because the population was read off the sources by whoever
 * was looking. What a class file carries is every place that takes the two, whatever it is called
 * and wherever it was written; reading it is {@link WhatSourceWrote}'s, which is where the two
 * texts a class file keeps are put back together.
 */
class NothingTakesANumberAndAnotherNumbersOrdersTest {

    private static final List<String> ORDERS = List.copyOf(
            WhatWasCompiled.everyKindOf("souther.compiler.inputs.TermOrders"));

    /**
     * What names a number: the term itself, its cases, and the values built around one.
     *
     * <p>A wrapper counts. What makes two arguments a pairing is that each says which number it is
     * about, and {@code RealizationTarget} says it as plainly as a term does — so a reader handed
     * one of those and a pair of orders has the same two things to get right.
     */
    private static final List<String> TERM = Stream.of(
                    "souther.compiler.inputs.NumericTerm",
                    "souther.compiler.partition.RealizationTarget")
            .map(WhatWasCompiled::everyKindOf).flatMap(Set::stream).toList();

    /**
     * The one place the two are meant to be about two numbers, and it says so by its shape.
     *
     * <p>Moving a quantity is asked which number it is over and handed the answer for the one it
     * lands on, and those are two numbers on purpose. Everything else that takes both is a pairing
     * a caller chose. Named by what it is rather than by which classes do it, so an implementation
     * added is covered and a second reader of two numbers is not.
     */
    private static final String MOVES = "movedTo";

    @Test
    void nothingTakesBothWithoutProvingTheyAgree() {
        Set<String> takesBoth = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            String from = model.thisClass().asInternalName().replace('/', '.');
            if (ORDERS.contains(from)) {
                continue;   // what the pair says about itself is its own business
            }
            for (Carrier carrier : WhatSourceWrote.handedOver(model)) {
                if (!carrier.meetApart(TERM, ORDERS) || proves(carrier) || moves(carrier.where())) {
                    continue;
                }
                takesBoth.add(carrier.where());
            }
        }

        assertEquals(Set.of(), takesBoth,
                "a number and a pair of orders taken as two arguments are two arguments that can"
                        + " be about two numbers; take the pair, which names its number, or hold"
                        + " the two to each other");
    }

    /**
     * And the exception keeps the shape it was allowed for.
     *
     * <p>One number and one answer. A second number beside them would be the pairing again, under
     * the one name this does not report.
     */
    @Test
    void movingAQuantityIsAskedOneNumberAndHandedOneAnswer() {
        Set<String> exempted = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            for (Carrier carrier : WhatSourceWrote.handedOver(model)) {
                if (moves(carrier.where()) && carrier.meetApart(TERM, ORDERS)) {
                    exempted.add(carrier.where());
                }
            }
        }

        Set<String> shapes = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            String from = model.thisClass().asInternalName().replace('/', '.');
            for (MethodModel method : model.methods()) {
                // The declared move, not the lambdas inside one: a lambda's parameters are what it
                // captured, which is not a shape anybody wrote.
                if (exempted.contains(from + "#" + method.methodName().stringValue())) {
                    shapes.add(method.methodTypeSymbol().parameterList().stream()
                            .map(ClassDesc::displayName).toList().toString());
                }
            }
        }

        assertEquals(Set.of("[NumericTerm, TermOrders]"), shapes,
                "moving is asked the number it is over and handed the answer for the one it lands"
                        + " on, and nothing else");
    }

    /** Whether this is the move, including the lambdas written inside one. */
    private static boolean moves(String where) {
        String method = where.substring(where.indexOf('#') + 1);
        return method.equals(MOVES) || method.startsWith(MOVES + " ");
    }

    /** That the scan is reading places at all, so an empty answer means what it says. */
    @Test
    void theScanReadsTheMethodsItIsAbout() {
        Set<String> carrying = new TreeSet<>();
        for (ClassModel model : WhatWasCompiled.compiled().all()) {
            for (Carrier carrier : WhatSourceWrote.handedOver(model)) {
                if (carrier.names(ORDERS)) {
                    carrying.add(carrier.where());
                }
            }
        }

        int found = carrying.size();
        assertTrue(found > 20,
                () -> "the scan found only " + found + " places taking a pair of orders,"
                        + " which is not this compiler");
    }

    /**
     * Whether it holds the two to each other, which is what {@link TermOrders#areOf} is.
     *
     * <p>Asked of everything compiled for the carrier, which for a method is its own code and the
     * code of the lambdas written inside it. A rule met in a lambda a method wrote is a rule that
     * method met; reading its own code alone would report a method for what the closure it wrote
     * plainly does.
     */
    private static boolean proves(Carrier carrier) {
        for (CodeModel code : carrier.bodies()) {
            for (var element : code) {
                if (element instanceof InvokeInstruction call
                        && ORDERS.contains(call.owner().asInternalName().replace('/', '.'))
                        && call.name().stringValue().equals("areOf")) {
                    return true;
                }
            }
        }
        return false;
    }


}
