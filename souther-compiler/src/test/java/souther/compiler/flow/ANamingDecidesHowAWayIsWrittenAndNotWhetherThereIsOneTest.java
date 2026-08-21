package souther.compiler.flow;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Swapping the naming moves what a way is called and nothing else.
 *
 * <p>The claim the whole separation rests on, and it is a structure rather than a hope: what the body
 * does is read with no naming at all, and a naming reaches only the list of ways. Checked all the
 * same, because the structure is one a later change could give up without anything else noticing.
 *
 * <p>Three namings beside the plain one, and each of them is a way a naming can fall short. One names
 * everything and so refuses ways nothing else refuses. One names nothing and so leaves every way
 * partial. One counts two forks on the same name as one decision, which is what the coverage
 * numbering does and is where this went wrong before: a body whose two arms contradict left that
 * naming with no way at all, and the reading answered that no value arrives — while the reading with
 * no numbering behind it, which does not follow that correlation, answered that one does.
 *
 * <p>And the list is held to the other half rather than allowed to speak for it. An enumeration of
 * the ways to a truth that holds none of them says the value is never settled that way, so it is only
 * ever answered where the reading of what the body does agrees.
 */
class ANamingDecidesHowAWayIsWrittenAndNotWhetherThereIsOneTest {

    /**
     * Bodies with the shapes this reading tells apart, beside what the corpus is written with.
     *
     * <p>The corpus is what the language is checked against and is written to be ordinary. What
     * decides this claim is the shapes where a naming has something to lose: an operator stopping on
     * a side the reading worked a value out for, a chain of them, an arm nothing reaches, and a
     * helper spliced in so that a position arrives under a name of its own.
     */
    private static final List<String> WRITTEN = List.of("""
            module example.fee

            data Amount = Int
            data Answer = Int

            behavior fee : (a: Amount, c: Amount, d: Amount) -> Answer
                constructs Answer

            let fee (a, c, d) =
                Answer(if a.value > 1 && unreachable "no large a reaches here"
                    then 0
                    else (if c.value > 3 then 1 else 0) + (if d.value > 4 then 10 else 0))
            """,
            """
            module example.chain

            data Amount = Int
            data Answer = Int

            behavior rank : (a: Amount, b: Amount) -> Answer
                constructs Answer

            let rank (a, b) =
                Answer(if a.value > 1 && a.value < 9 && b.value /= 0 then 1
                    else if a.value > 1 || b.value > 2 then 2
                    else 3)
            """,
            """
            module example.arms

            data On
            data Off
            data Flag = On | Off
            data Answer = Int

            behavior pick : (f: Flag, g: Flag) -> Answer
                constructs Answer

            let pick (f, g) =
                Answer(match f with
                    | On -> match g with
                        | On -> 1
                        | Off -> unreachable "an Off never arrives beside an On"
                    | Off -> 2)
            """,
            """
            module example.shipping

            data Total = Int
                invariant value >= 0
                invariant value <= 1000000

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))
            """,
            """
            module example.opposed

            data On
            data Off
            data Flag = On | Off

            behavior pick : (a: Flag) -> Int

            let pick (a) =
                if ((match a with | On -> true | Off -> false)
                        && (match a with | On -> false | Off -> true))
                        || unreachable "the operator above never comes to false"
                    then 1
                    else 2
            """);

    @Test
    void everyBodyIsReadTheSameWhateverItsWaysAreCalled() {
        Read read = new Read();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            bodiesOf(corpus).forEach(body -> compare(body, read));
        }
        for (String source : WRITTEN) {
            bodiesOf(source).forEach(body -> compare(body, read));
        }
        // Not a measure of anything, and here so that a claim about what two readings agree on is not
        // quietly a claim about two readings that read nothing. What the shapes above were written
        // for is the second of these: a value this reading works a truth out for is where a naming
        // has something to lose, and a run with none of them agrees for no reason.
        assertTrue(read.nodes > 100, "something was put in front of this: " + read.nodes + " nodes");
        assertTrue(read.valued > 10,
                "some of it was a value this reading works a truth out for: " + read.valued);
    }

    /** How much was read, so that agreement about nothing is not mistaken for agreement. */
    private static final class Read {
        private int nodes;
        private int valued;
    }

    /** Every node of {@code body}, read four ways and compared. */
    private void compare(Core body, Read read) {
        ValueArrivals<AnonymousPath> plain = ValueArrivals.ofBody(body, Anonymous.NAMING);
        List<ValueArrivals<Marks>> others = List.of(
                ValueArrivals.ofBody(body, new Marking(Marking.Words.EVERY, false)),
                ValueArrivals.ofBody(body, new Marking(Marking.Words.NONE, false)),
                ValueArrivals.ofBody(body, new Marking(Marking.Words.EVERY, true)));
        List<Core> all = new ArrayList<>();
        each(body, all);
        read.nodes += all.size();
        for (Core node : all) {
            Comes loose = plain.comesAt(node);
            if (!loose.known().isEmpty()) {
                read.valued++;
            }
            for (ValueArrivals<Marks> other : others) {
                assertEquals(loose.truths(), other.comesAt(node).truths(),
                        "a naming moved what the body does at a "
                                + node.getClass().getSimpleName());
                for (boolean want : List.of(true, false)) {
                    if (other.waysTo(node, want) instanceof Ways.Known<Marks> known
                            && known.paths().isEmpty()) {
                        assertFalse(loose.mayCome(want),
                                "an enumeration holding no way said a value the body comes to is "
                                        + "never settled that way, at a "
                                        + node.getClass().getSimpleName());
                    }
                }
            }
        }
    }

    private static void each(Core node, List<Core> into) {
        into.add(node);
        Core.forEachChild(node, child -> {
            if (child != null) {
                each(child, into);
            }
        });
    }

    private static List<Core> bodiesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return bodiesIn(compilation, source);
    }

    private static List<Core> bodiesOf(ConformanceCorpus corpus) {
        return bodiesIn(corpus.analyse().compilation(), corpus.toString());
    }

    private static List<Core> bodiesIn(Compilation compilation, String what) {
        List<Core> out = new ArrayList<>();
        compilation.modules().forEach(module -> {
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            if (checked != null) {
                checked.behaviorBodies().values().stream().filter(body -> body != null)
                        .forEach(out::add);
            }
        });
        assertFalse(out.isEmpty(), "the model under test has behavior bodies: " + what);
        return out;
    }

    /** The conditions on a way, written out as whatever named them. */
    private record Marks(List<String> of) { }

    /**
     * A naming with words for everything or for nothing, telling decisions apart by the node or by
     * the name the node is about.
     *
     * <p>Four namings out of two choices, and each choice is a way a naming falls short. Words for
     * nothing leaves every way partial and refuses none. Words for everything refuses ways the
     * coverage numbering never sees. Telling two forks on one name apart is what a naming keyed on
     * the node does; running them together is what a naming keyed on the position does, and that is
     * the coverage numbering — two {@code match a} in one body are two places and one decision, so a
     * way through opposite arms of them is no way and comes out.
     */
    private static final class Marking implements Naming<Marks> {

        /** Whether this naming has words for a condition at all. */
        private enum Words { EVERY, NONE }

        private final Words words;
        private final boolean byName;
        private final IdentityHashMap<Core, Integer> numbered = new IdentityHashMap<>();

        private Marking(Words words, boolean byName) {
            this.words = words;
            this.byName = byName;
        }

        @Override
        public Marks nowhere() {
            return new Marks(List.of());
        }

        @Override
        public Marks join(Marks held, Marks more) {
            TreeSet<String> both = new TreeSet<>(held.of());
            for (String each : more.of()) {
                String decision = each.substring(0, each.lastIndexOf('/') + 1);
                for (String already : both) {
                    if (already.startsWith(decision) && !already.equals(each)) {
                        return null;   // one decision, two ways out of it, and no run doing both
                    }
                }
                both.add(each);
            }
            return new Marks(List.copyOf(both));
        }

        @Override
        public Naming<Marks> under(Hir.Binder binder, Core value) {
            return this;
        }

        @Override
        public Marks side(Core value, boolean held) {
            return mark(value, value instanceof Core.Binary comparison ? comparison.left() : value,
                    "cmp", held ? 1 : 0);
        }

        @Override
        public Marks matchCase(Core.Match match, int part) {
            return mark(match, match.scrutinee(), "case", part);
        }

        @Override
        public Marks forkArm(Core fork, int part) {
            return mark(fork, fork instanceof Core.If iff ? iff.cond() : fork, "arm", part);
        }

        private Marks mark(Core at, Core about, String what, int part) {
            if (words == Words.NONE) {
                return null;
            }
            String which = byName && about instanceof Core.Read read
                    ? read.binding().toString()
                    : String.valueOf(numbered.computeIfAbsent(at, ignored -> numbered.size()));
            return new Marks(List.of(what + "@" + which + "/" + part));
        }

        @Override
        public int mostArrivals() {
            return 64;
        }
    }
}
