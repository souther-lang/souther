package souther.compiler.flow;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Swapping the naming moves what a way is called and nothing else.
 *
 * <p>The claim the whole separation rests on. Before it, a comparison the numbering could not place
 * was answered as a comparison with no value, so everything standing under it was read as reaching
 * nothing — a limit of what could be written down turning into a claim about what the body does.
 *
 * <p>So two readings of one body are taken here and what they agree about is checked rather than
 * described: every node arrives in one exactly where it arrives in the other, and a truth one of them
 * worked out is a truth the reading with no numbering behind it worked out too. A naming may leave a
 * way {@link Completeness#PARTIAL} and it may see that two conditions on a way settle one decision
 * opposite ways and drop it — the second is why a truth may be missing where the reading answers that
 * it has nothing to say, and never why one may be there that the body has not got.
 *
 * <p>Two namings beside the plain one, so both directions are covered: one that names everything and
 * so refuses more ways than the coverage numbering ever will, and one that names nothing and so
 * leaves every way partial.
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
            """);

    /** What a reading says about one node, in the words every reading of it has. */
    private record Says(boolean arrives, Set<Truth> comesTo) { }

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

    /** Every node of {@code body}, read three ways and compared. */
    private void compare(Core body, Read read) {
        ValueArrivals<AnonymousPath> plain = ValueArrivals.ofBody(body, Anonymous.NAMING);
        List<ValueArrivals<Marks>> others =
                List.of(ValueArrivals.ofBody(body, new Marking(true)),
                        ValueArrivals.ofBody(body, new Marking(false)));
        List<Core> all = new ArrayList<>();
        each(body, all);
        read.nodes += all.size();
        for (Core node : all) {
            Says loose = says(plain.at(node));
            if (loose.comesTo().contains(Truth.TRUE) || loose.comesTo().contains(Truth.FALSE)) {
                read.valued++;
            }
            for (ValueArrivals<Marks> other : others) {
                Says tight = says(other.at(node));
                assertEquals(loose.arrives(), tight.arrives(),
                        "a naming decided whether a " + node.getClass().getSimpleName()
                                + " arrives at a value");
                for (Truth each : tight.comesTo()) {
                    assertTrue(each == Truth.UNREAD || loose.comesTo().contains(each),
                            "a naming worked out a value nothing else could: " + each + " at a "
                                    + node.getClass().getSimpleName());
                }
            }
        }
    }

    private static <P> Says says(Set<Arrival<P>> arrivals) {
        Set<Truth> comesTo = new LinkedHashSet<>();
        arrivals.forEach(each -> comesTo.add(each.value()));
        return new Says(!arrivals.isEmpty(), comesTo);
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
     * A naming with words for everything, or for nothing.
     *
     * <p>The first is stricter than the coverage numbering, which has words for a fork the plan named
     * and for a comparison it could place and for nothing else: every way that one refuses this
     * refuses too, and it refuses ways besides. The second is the other end — every way partial,
     * nothing ever refused — and between them they move every part of a naming that can move.
     */
    private static final class Marking implements Naming<Marks> {

        private final boolean names;
        private final IdentityHashMap<Core, Integer> numbered = new IdentityHashMap<>();

        private Marking(boolean names) {
            this.names = names;
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
        public Marks side(Core.Binary comparison, boolean held) {
            return mark(comparison, "cmp", held ? 1 : 0);
        }

        @Override
        public Marks matchCase(Core.Match match, int part) {
            return mark(match, "case", part);
        }

        @Override
        public Marks forkArm(Core fork, int part) {
            return mark(fork, "arm", part);
        }

        private Marks mark(Core at, String what, int part) {
            if (!names) {
                return null;
            }
            int which = numbered.computeIfAbsent(at, ignored -> numbered.size());
            return new Marks(List.of(what + "@" + which + "/" + part));
        }

        @Override
        public int mostArrivals() {
            return 64;
        }
    }
}
