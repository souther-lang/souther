package souther.bench;

import org.junit.jupiter.api.Test;

import souther.bench.SaltedOrder.Finding;
import souther.bench.SaltedOrder.Reading;
import souther.bench.readings.orders.AskedOrNamedInOrder;
import souther.bench.readings.orders.Held;
import souther.bench.readings.orders.HeldClasses;
import souther.bench.readings.orders.ReadersAfter;
import souther.bench.readings.orders.ReadersBefore;
import souther.bench.readings.orders.WalkedIntoAnAnswer;
import souther.test.CompiledClasses;

import java.lang.classfile.ClassModel;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the walk that follows an unordered copy finds, over readers written to be found.
 *
 * <p>The rule about the compiler's own copies is only as good as this: it says there is no reader
 * that takes an order off a copy, and a walk that could not find one would say so of any code. So
 * it is put to readers that do, and to readers that only look like they do, before what it says of
 * the compiler means anything.
 *
 * <p><b>The readers are the methods of the classes, not a list.</b> A way of taking an order added
 * to {@link WalkedIntoAnAnswer} is asked about by being there, and one added to
 * {@link AskedOrNamedInOrder} is asked to be passed.
 */
class TheReadingOfWhereAnUnorderedCopysOrderGoesTest {

    private static final String FIXTURES = "souther.bench.readings.orders";

    private static boolean madeInTheFixtures(String className) {
        return className.startsWith("souther/bench/readings/orders/");
    }

    @Test
    void everyWayOfTakingTheOrderOffACopyIsFoundInTheReaderThatDoesIt() {
        Reading reading = readingOver(WalkedIntoAnAnswer.class);
        Set<String> readers = publicMethodsOf(WalkedIntoAnAnswer.class);
        assertFalse(readers.isEmpty(), "the class of readers to be refused holds none");

        List<String> passed = new ArrayList<>();
        for (String reader : readers) {
            if (findingsIn(reading, WalkedIntoAnAnswer.class, reader).isEmpty()) {
                passed.add(reader);
            }
        }

        assertEquals(List.of(), passed,
                "a reader took the order of a copy into an answer and the walk let it by — so the"
                        + " same reader written in the compiler is let by too");
    }

    @Test
    void noWayOfNamingTheOrderFirstOrOfNeverAskingItIsTakenForTakingIt() {
        Reading reading = readingOver(AskedOrNamedInOrder.class);
        assertFalse(publicMethodsOf(AskedOrNamedInOrder.class).isEmpty(),
                "the class of readers to be passed holds none");

        assertEquals(List.of(), reading.described(),
                "a reader that puts the copy in an order, or asks it what it holds, was refused"
                        + " for walking it");
    }

    /**
     * And the passing is by following the copy to where it is put in an order, not by not seeing
     * it.
     *
     * <p>Held apart from the check above because a walk that lost every copy at the first call
     * would pass every reader in that class too. What says otherwise is where each of them is
     * reported to have ended.
     */
    @Test
    void theCopiesThePassedReadersWalkAreReportedToEndWhereTheyWereGiven() {
        Reading reading = readingOver(AskedOrNamedInOrder.class);
        Set<String> ends = new LinkedHashSet<>();
        reading.reached().values().forEach(ends::addAll);

        for (String crossing : List.of(
                "put in an order by souther.compiler.publish.CanonicalSelection$Order.keep",
                "put in an order by souther.compiler.inputs.NumericTerms.inOrder",
                "put in an order by java.util.EnumSet",
                "put in an order by java.util.TreeMap",
                "put in an order by java.util.stream.Stream.sorted",
                "put in an order by java.util.List.sort",
                "folded by souther.compiler.query.WeakeningSet.ofAll",
                "read as asked what it holds",
                "read as the message of java.lang.IllegalStateException")) {
            assertTrue(ends.contains(crossing),
                    () -> "no copy was followed to " + crossing + ", so what passed the readers"
                            + " that end there was not read: " + ends);
        }
    }

    @Test
    void aMethodCalledLikeACrossingIsNotOneWhereItIsDeclaredElsewhere() {
        Reading reading = readingOver(WalkedIntoAnAnswer.class);

        assertFalse(findingsIn(reading, WalkedIntoAnAnswer.class, "namedByAnImpostor").isEmpty(),
                "a method called keep that takes a collection was taken for the one that puts a"
                        + " collection in an order, so a name is all a crossing needs to be");
    }

    /**
     * A reader that is replaced by another is the one the walk names, however many there are.
     *
     * <p>The count of the readers of a copy is the same before and after, and a check that held
     * the count would hold it at two. The walk reads what each does, so it is quiet over the first
     * and names the reader that was written in place of the second.
     */
    @Test
    void aReaderWrittenInPlaceOfAnotherIsTheOneThatIsNamedAndTheCountIsUnchanged() {
        List<ClassModel> before = fixtures(Held.class, ReadersBefore.class);
        List<ClassModel> after = fixtures(Held.class, ReadersAfter.class);

        assertEquals(2, readersOfHeld(before, ReadersBefore.class),
                "the readers before were meant to be two");
        assertEquals(readersOfHeld(before, ReadersBefore.class),
                readersOfHeld(after, ReadersAfter.class),
                "the two are meant to have as many readers, or the swap says nothing about counts");

        Reading quiet = SaltedOrderFlow.read(before,
                TheReadingOfWhereAnUnorderedCopysOrderGoesTest::madeInTheFixtures);
        Reading named = SaltedOrderFlow.read(after,
                TheReadingOfWhereAnUnorderedCopysOrderGoesTest::madeInTheFixtures);

        assertEquals(List.of(), quiet.described(), "the readers that put a copy in order were"
                + " refused");
        assertEquals(1, named.findings().size(), () -> "the reader written in place of the other"
                + " was not the one named: " + named.described());
        assertTrue(named.findings().get(0).reader()
                        .startsWith(ReadersAfter.class.getName() + "#theTerms("),
                () -> "the reader that was named was not the one that was swapped in: "
                        + named.described());
    }

    @Test
    void theCopiesTheFixturesMakeAreTheOnesTheReadingBeginsAt() {
        Reading reading = readingOver(AskedOrNamedInOrder.class);

        assertEquals(6, reading.roots().size(),
                () -> "the copies made by the model are the ones it begins at: " + reading.roots());
        assertTrue(reading.roots().stream()
                        .allMatch(each -> each.startsWith(Held.class.getName() + "#<init>")
                                || each.startsWith(HeldClasses.class.getName() + "#<init>")),
                () -> "a copy from somewhere other than the model was read: " + reading.roots());
    }

    private static Reading readingOver(Class<?> readers) {
        return SaltedOrderFlow.read(fixtures(Held.class, HeldClasses.class, readers),
                TheReadingOfWhereAnUnorderedCopysOrderGoesTest::madeInTheFixtures);
    }

    /** The classes, as they were compiled, of the ones named. */
    private static List<ClassModel> fixtures(Class<?>... these) {
        CompiledClasses compiled = CompiledClasses.ofModule(
                TheReadingOfWhereAnUnorderedCopysOrderGoesTest.class);
        List<String> names = Arrays.stream(these).map(Class::getName).toList();
        List<ClassModel> found = new ArrayList<>();
        for (ClassModel each : compiled.inPackage(FIXTURES)) {
            String name = each.thisClass().asInternalName().replace('/', '.');
            if (names.stream().anyMatch(wanted -> name.equals(wanted)
                    || name.startsWith(wanted + "$"))) {
                found.add(each);
            }
        }
        assertEquals(names.size(), found.stream().map(each -> each.thisClass().asInternalName())
                        .filter(each -> !each.contains("$")).count(),
                () -> "a class of the fixtures was not read: " + names);
        return found;
    }

    private static Set<String> publicMethodsOf(Class<?> holder) {
        Set<String> out = new LinkedHashSet<>();
        for (Method each : holder.getDeclaredMethods()) {
            if (Modifier.isPublic(each.getModifiers()) && Modifier.isStatic(each.getModifiers())) {
                out.add(each.getName());
            }
        }
        return out;
    }

    private static List<Finding> findingsIn(Reading reading, Class<?> holder, String method) {
        List<Finding> out = new ArrayList<>();
        for (Finding each : reading.findings()) {
            if (each.reader().startsWith(holder.getName() + "#" + method)) {
                out.add(each);
            }
        }
        return out;
    }

    /** How many methods of {@code readers} ask the model for what a copy made. */
    private static long readersOfHeld(List<ClassModel> classes, Class<?> readers) {
        Set<String> asked = Set.of("figures", "named", "terms", "weakenings");
        return Compiled.sitesIn(classes).stream()
                .filter(each -> each.from().equals(readers.getName())
                        && each.how() == Compiled.How.CALLS
                        && each.owner().equals(Held.class.getName())
                        && asked.contains(each.member()))
                .map(Compiled.Site::at).distinct().count();
    }
}
