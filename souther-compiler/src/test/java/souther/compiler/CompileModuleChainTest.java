package souther.compiler;


import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior may be imported and composed two hops away (spec §modules, §composition): module {@code c} composes
 * {@code b}'s {@code twice}, whose own definition composes {@code a}'s {@code inc}. Resolving
 * {@code twice}'s signature for {@code c} has to resolve {@code b}'s imports in turn, not just
 * {@code b}'s own definitions — an import chain deeper than one hop.
 */
class CompileModuleChainTest {

    private static final String A = """
            module a exposing ( N, inc )
            data N = Int
            behavior inc : (n: N) -> N
            let inc (n) = n
            """;
    private static final String B = """
            module b exposing ( twice : N )
            import a ( N, inc )
            behavior twice = inc >-> inc
            """;
    // c imports N as well: its generated `quad` carries a `Behavior<N, N>` signature (spec §jvm-anonymous-union,
    // 24), so N's class must be nameable here — the same reason Java code importing a generic method
    // imports its type arguments.
    private static final String C = """
            module c
            import a ( N )
            import b ( twice )
            behavior quad = twice >-> twice
            """;

    @Test
    void composesABehaviorTwoImportHopsAway() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(A, B, C));
        assertTrue(classes.containsKey("c.Quad"), "the two-hop composition generates c.Quad");

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object five = Codecs.decoded(loader, "a.N", 5L);
        Object quad = loader.loadClass("c.Quad" + "$Impl").getConstructor().newInstance();
        Object r = Codecs.apply(quad, five);

        assertEquals(5L, Codecs.encode(loader, "a.N", r), "inc is identity, so quad round-trips 5 through the chain");
    }

    // A `>->` whose departed case comes from an imported behavior: the case's own class cannot
    // implement a union declared here, so it joins through the bridge case this module emits.
    private static final String PA = """
            module pa exposing ( Priced, Empty, price )
            data Priced = { total: Int }
            data Empty
            behavior price : (amount: Int) -> Priced | Empty
                constructs Priced, Empty
            let price (amount) = if amount > 0 then Priced { total = amount } else Empty
            """;
    private static final String PB = """
            module pb
            import pa ( Priced, Empty, price )
            data Receipt = { total: Int }
            behavior bill : (p: Priced) -> Receipt
                constructs Receipt
            let bill (p) = Receipt { total = p.total }
            behavior checkout = price >-> bill
            """;

    @Test
    void aDepartedImportedCaseReachesTheCompositionsUnionThroughABridgeCase() throws Exception {
        // checkout's output is Receipt | Empty. Receipt is pb's own and is the case itself; Empty is
        // pa's, so pb emits pb.EmptyCase and permits that.
        Map<String, byte[]> classes = Compiler.compileModules(List.of(PA, PB));
        BytesClassLoader loader = new BytesClassLoader(classes, CompileModuleChainTest.class.getClassLoader());
        assertEquals(List.of(loader.loadClass("pb.EmptyCase"), loader.loadClass("pb.Receipt")),
                Arrays.asList(loader.loadClass("pb.CheckoutResult").getPermittedSubclasses()));

        Object checkout = loader.loadClass("pb.Checkout").getMethod("of").invoke(null);
        assertEquals("pb.Receipt", Codecs.apply(checkout, 300L).getClass().getName(),
                "the mainline runs to the last stage and answers with this module's own case");

        Object departed = Codecs.apply(checkout, 0L);
        assertEquals("pb.EmptyCase", departed.getClass().getName(),
                "the imported case departs at the first stage and joins the union bridged");
        assertEquals("pa.Empty",
                departed.getClass().getMethod("value").invoke(departed).getClass().getName());
    }
}
