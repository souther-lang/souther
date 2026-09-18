package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatSourceWrote.Carrier;

import java.lang.classfile.ClassModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link WhatSourceWrote} makes of each shape a compiler lowers a source to.
 *
 * <p>The rules that use it are about types this compiler declares, and each of them is green when
 * nothing offends. So a shape the reading gets wrong is a shape those rules are quiet about, and
 * every way a class file can say something other than what was written had to be found by somebody
 * reading the reading. Here each of them is a value, written the way it would be written, and what
 * the reading makes of it is said out loud.
 *
 * <p><b>Two ordinary types stand in for the two.</b> What a rule pairs is its own; what this is
 * about is whether a value was written and what it names, which is the same question whatever the
 * types are. Using a string and a number keeps this from passing because of anything true of this
 * compiler's own.
 */
class WhatSourceWroteTest {

    private static final List<String> LEFT = List.of("java.lang.String");
    private static final List<String> RIGHT = List.of("java.lang.Integer");

    /** Written as a record: two components, both somebody's. */
    record Written(String one, Integer two) { }

    /** A list of the one beside the other, which only a reading through wrapping sees. */
    record UnderWrapping(List<String> one, Integer two) { }

    /** What a class holds is not what an instance holds. */
    static final class OfTheClassAndOfAnInstance {
        static final String ONE = "";

        private final Integer two = 0;

        Integer two() {
            return two;
        }
    }

    /** A value under a variable bounded by a list of the one. */
    static <N extends List<String>> String underAVariable(N one, Integer two) {
        return one + ":" + two;
    }

    /** And the same where the variable is declared by the class this is written inside. */
    static final class Around<N extends List<String>> {
        final class Inside {
            private final N one = null;

            private final Integer two = 0;

            String use() {
                return one + ":" + two;
            }
        }
    }

    /**
     * What an inner class is handed of the class it is inside, which nobody wrote.
     *
     * <p>Standing in one is the whole of what this is: it reads what it is inside, so that it is
     * the kind of class whose constructor is handed that instance.
     */
    final class Inner {
        private final Integer two;

        Inner(Integer two) {
            this.two = two;
        }

        String use() {
            return around() + two;
        }
    }

    private String around() {
        return getClass().getSimpleName();
    }

    static String bothClosedOver(String one) {
        Integer two = one.length();
        Supplier<String> made = () -> one + ":" + two;
        return made.get();
    }

    static String oneClosedOverAndOneHanded(Integer two) {
        Function<String, String> made = one -> one + ":" + two;
        return made.apply("");
    }

    static String bothClosedOverByALocalClass(String one) {
        Integer two = one.length();
        class Both {
            String use() {
                return one + ":" + two;
            }
        }
        return new Both().use();
    }

    static String oneClosedOverAndOneTakenByALocalClass(Integer two) {
        class Mixed {
            private final String one;

            Mixed(String one) {
                this.one = one;
            }

            String use() {
                return one + ":" + two;
            }
        }
        return new Mixed("").use();
    }

    static String written(String one, Integer two) {
        return one + ":" + two;
    }

    static BiFunction<String, Integer, String> named() {
        return WhatSourceWroteTest::written;
    }

    @Test
    void whatWasWrittenIsRead() {
        assertTrue(handedOverBy(Written.class, "<init>").meetApart(LEFT, RIGHT),
                "two components are two places somebody wrote");
        assertTrue(heldBy(Written.class).meetApart(LEFT, RIGHT),
                "a record's components are what it holds");
        assertTrue(handedOverBy(UnderWrapping.class, "<init>").meetApart(LEFT, RIGHT),
                "a list of the one is the one, or a reading is blind to the plainest wrapping");
        assertTrue(handedOverBy(WhatSourceWroteTest.class, "written").meetApart(LEFT, RIGHT),
                "two parameters are two places somebody wrote");
    }

    @Test
    void aVariableStandsForWhatItWasBoundedBy() {
        assertTrue(handedOverBy(WhatSourceWroteTest.class, "underAVariable").meetApart(LEFT, RIGHT),
                "a value under a variable bounded by a list of the one names the one");
        assertTrue(heldBy(Around.Inside.class).meetApart(LEFT, RIGHT),
                "the variable is declared by the class this one is written inside, and a reading"
                        + " that stopped at the class in hand would name nothing");
    }

    @Test
    void whatTheClassHoldsIsNotWhatAnInstanceHolds() {
        List<Carrier> held = WhatSourceWrote.held(read(OfTheClassAndOfAnInstance.class));
        assertEquals(2, held.size(), "one place for the class and one for an instance: " + where(held));
        for (Carrier each : held) {
            assertTrue(!each.meet(LEFT, RIGHT),
                    () -> "a constant of the class stands beside every instance there will be, and"
                            + " no instance holds both: " + each.where());
        }
    }

    @Test
    void whatNobodyWroteIsNotAPlaceSomebodyChose() {
        assertTrue(!aLambdaIn(WhatSourceWroteTest.class, "bothClosedOver").meet(LEFT, RIGHT),
                "two locals a closure took are two locals of one scope");
        assertTrue(!heldBy(loweredIn("bothClosedOverByALocalClass", "Both")).meet(LEFT, RIGHT),
                "and the same where the closure is a class");
        assertTrue(!handedOverBy(WhatSourceWroteTest.class, "bothClosedOver").meet(LEFT, RIGHT),
                "the method itself is handed one of them and not the other");
    }

    @Test
    void oneWrittenBesideOneClosedOverIsAPlaceSomebodyChose() {
        assertTrue(aLambdaIn(WhatSourceWroteTest.class, "oneClosedOverAndOneHanded")
                        .meetApart(LEFT, RIGHT),
                "what the lambda is handed is somebody's, and it stands beside what it closed over");
        assertTrue(heldBy(loweredIn("oneClosedOverAndOneTakenByALocalClass", "Mixed"))
                        .meetApart(LEFT, RIGHT),
                "a field somebody wrote beside a field lowering made is the same choice");
    }

    @Test
    void whatAnInnerClassIsHandedOfWhereItStandsIsNotSomebodysChoice() {
        Carrier made = handedOverBy(Inner.class, "<init>");
        assertTrue(made.names(List.of(WhatSourceWroteTest.class.getName())),
                "an inner class is handed the instance it is inside");
        assertTrue(!made.sourceNames(List.of(WhatSourceWroteTest.class.getName())),
                "and nobody wrote it: what says so is the attribute whose subject that is");
        assertTrue(made.sourceNames(RIGHT), "while the parameter beside it is written");
    }

    @Test
    void namingAMethodIsNotWritingOne() {
        List<String> lambdas = new ArrayList<>();
        for (Carrier each : WhatSourceWrote.handedOver(read(WhatSourceWroteTest.class))) {
            if (each.where().endsWith(")") && each.where().contains("#named")) {
                lambdas.add(each.where());
            }
        }
        assertEquals(List.of(), lambdas,
                "a reference to a method that was written is read where that method is declared;"
                        + " reading it here too would report the place that named it for a shape"
                        + " somebody else wrote");
    }

    /** That the fixtures are being read at all, so what is asserted above is asserted of something. */
    @Test
    void theReadingReachesTheShapesThisIsAbout() {
        Set<String> read = new TreeSet<>();
        for (Carrier each : WhatSourceWrote.handedOver(read(WhatSourceWroteTest.class))) {
            read.add(each.where());
        }
        assertTrue(read.size() > 8, () -> "the reading found only " + read + " here");
        assertTrue(read.stream().anyMatch(each -> each.contains("(a lambda written in it)")),
                () -> "no lambda among them, so what is said about one says nothing: " + read);
    }

    private static Carrier heldBy(Class<?> of) {
        return heldBy(read(of));
    }

    private static Carrier heldBy(ClassModel of) {
        List<Carrier> held = WhatSourceWrote.held(of);
        assertEquals(1, held.size(), "one place: " + where(held));
        return held.getFirst();
    }

    private static Carrier handedOverBy(Class<?> of, String named) {
        return one(WhatSourceWrote.handedOver(read(of)), "#" + named, of + "#" + named);
    }

    private static Carrier aLambdaIn(Class<?> of, String named) {
        return one(WhatSourceWrote.handedOver(read(of)),
                "#" + named + " (a lambda written in it)", of + "#" + named + "'s lambda");
    }

    private static Carrier one(List<Carrier> among, String ending, String asked) {
        List<Carrier> found = among.stream().filter(each -> each.where().endsWith(ending)).toList();
        assertEquals(1, found.size(), "one carrier for " + asked + ": " + where(found));
        return found.getFirst();
    }

    /** The class a method's local class was lowered to, named the way javac names one. */
    private static ClassModel loweredIn(String method, String written) {
        String named = WhatSourceWroteTest.class.getName() + "$1" + written;
        ClassModel found = WhatWasCompiled.checksCompiledBesideIt().find(named).orElse(null);
        assertTrue(found != null, () -> "the class written in " + method + " is not among what was"
                + " compiled beside this, under the name javac gives one: " + named);
        return found;
    }

    private static ClassModel read(Class<?> of) {
        return WhatWasCompiled.checksCompiledBesideIt().find(of.getName())
                .orElseThrow(() -> new IllegalStateException(of + " was not compiled beside this"));
    }

    private static List<String> where(List<Carrier> among) {
        return among.stream().map(Carrier::where).toList();
    }
}
