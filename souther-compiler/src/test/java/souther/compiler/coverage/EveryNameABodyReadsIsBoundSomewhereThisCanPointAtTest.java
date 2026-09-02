package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every name a body reads is bound at a place this can point at, and the same place in two compiles
 * of one source.
 *
 * <p>What {@link BinderAddress} is for. A {@code BindingId} says a binder and its reads are one
 * thing, which is what the passes need; what it is made of is an owner and a count, and an expansion
 * owns the copies it makes and numbers them as it makes them. So a reading of a body that carried
 * the id would move when nothing about the body did, and a reading that dropped it could not say
 * which of two names a read meant.
 *
 * <p><b>The refusal is the point of the third arm not existing.</b> A read this cannot place is a
 * body reading a name nothing in sight binds. If that happens, what a reader of these addresses
 * wants is to be told, not to be handed a place that was invented for the occasion — so it throws,
 * and this is where the corpus says whether it ever has to.
 */
class EveryNameABodyReadsIsBoundSomewhereThisCanPointAtTest {

    private static final String SPLICED = """
            module demo

            let picked (n: Int, cap: Int): List<Int> = {
                let ceiling = cap + 1
                [ n | n >= 240, n <= ceiling ]
            }

            behavior over : (a: Int, b: Int) -> List<Int>
            let over (a, b) = picked(a, b) ++ picked(b, a)
            """;

    private static final String BINDING_SHAPES = """
            module demo

            data Warm = Int invariant hot = value >= 240
            data Low
            data UnderThirty
            data ThirtyOrOver
            data Band = UnderThirty | ThirtyOrOver

            behavior attempt : (t: Int) -> Warm | Low
                constructs Warm
            let attempt (t) = if Warm(t) as w then w else Low

            behavior matched : (band: Band) -> Int
            let matched (band) =
                match band with
                    | UnderThirty -> 1
                    | ThirtyOrOver -> 2

            behavior kept : (xs: List<Int>) -> List<Int>
            let kept (xs) = List.filter(x -> x >= 240, xs)
            """;

    @Test
    void everyReadIsPlaced() {
        Set<String> arms = new LinkedHashSet<>();
        int reads = 0;
        for (Body body : everyBody()) {
            NodeAddresses places = NodeAddresses.of(body.behavior(), body.body());
            Binders binders = Binders.of(body.behavior(), body.body(), places);
            for (Core.Read read : readsIn(body.body())) {
                if (read.binding() == null) {
                    continue;
                }
                reads++;
                arms.add(binders.at(read.binding()).getClass().getSimpleName());
            }
        }

        assertTrue(reads > 0, "no name was read at all, so this says nothing");
        assertEquals(Set.of("Local", "Parameter"), arms,
                "both ways of being bound are met, so neither arm is here on a guess");
    }

    /** And a binder that moved only because a copy was numbered differently is at the same
     *  place. */
    @Test
    void twoCompilationsPlaceTheSameNamesAtTheSamePlaces() {
        for (String source : List.of(SPLICED, BINDING_SHAPES)) {
            assertEquals(placementsIn(source), placementsIn(source),
                    "where a body's names are bound does not move between two compiles of it");
        }
    }

    /**
     * The two splices of one helper bind their names at two places.
     *
     * <p>Which is the whole of what the id could not say: the copies are equal trees, so their
     * binders are alike in everything but where they stand, and the compiler tells them apart by
     * having numbered them as it made them.
     *
     * <p>Three names apiece and not one, the arguments being bound where the call was spliced: the
     * helper's two parameters and the {@code let} it writes. They stand one inside the next, so
     * what tells the three of one copy apart is how far down each is, and what tells a copy from
     * its twin is which side of the {@code ++} it was spliced into.
     */
    @Test
    void aSplicedHelpersNamesAreBoundOncePerSplice() {
        List<String> lets = placementsIn(SPLICED).stream()
                .filter(each -> each.endsWith(".let"))
                .sorted().toList();

        assertEquals(List.of(
                        "over/BinaryLeft.let",
                        "over/BinaryLeft/LetBody.let",
                        "over/BinaryLeft/LetBody/LetBody.let",
                        "over/BinaryRight.let",
                        "over/BinaryRight/LetBody.let",
                        "over/BinaryRight/LetBody/LetBody.let"),
                lets,
                "the helper's names, bound once per splice");
    }

    private static Set<String> placementsIn(String source) {
        Set<String> out = new LinkedHashSet<>();
        for (Body body : bodiesOf(List.of(List.of(source)))) {
            NodeAddresses places = NodeAddresses.of(body.behavior(), body.body());
            Binders binders = Binders.of(body.behavior(), body.body(), places);
            for (Core.Read read : readsIn(body.body())) {
                if (read.binding() != null) {
                    out.add(binders.at(read.binding()).toString());
                }
            }
        }
        return out;
    }

    private static List<Core.Read> readsIn(Core body) {
        List<Core.Read> out = new ArrayList<>();
        walk(body, new IdentityHashMap<>(), node -> {
            if (node instanceof Core.Read read) {
                out.add(read);
            }
        });
        return out;
    }

    private static void walk(Core e, Map<Core, Boolean> seen,
                             java.util.function.Consumer<Core> at) {
        if (seen.put(e, Boolean.TRUE) != null) {
            return;
        }
        at.accept(e);
        CoreStructure.childrenOf(e).forEach(child -> walk(child.node(), seen, at));
    }

    private record Body(String module, String behavior, Core body) {}

    private static List<Body> everyBody() {
        List<List<String>> sources = new ArrayList<>();
        ConformanceCorpus.all().forEach(corpus -> sources.add(corpus.sources()));
        sources.add(List.of(SPLICED));
        sources.add(List.of(BINDING_SHAPES));
        return bodiesOf(sources);
    }

    private static List<Body> bodiesOf(List<List<String>> sources) {
        List<Body> out = new ArrayList<>();
        for (List<String> each : sources) {
            Compilation compilation = Compilation.ofSources(each, ModulePath.EMPTY);
            compilation.answerEverything();
            int before = out.size();
            for (String module : compilation.modules()) {
                Bodies.Elaborated checked =
                        compilation.db().ask(new Bodies.Checked(module)).value();
                if (checked != null) {
                    checked.behaviorBodies().forEach((behavior, body) ->
                            out.add(new Body(module, behavior, body)));
                }
            }
            assertTrue(out.size() > before,
                    () -> "a source set compiled to no body at all: " + compilation.errors());
        }
        return out;
    }
}
