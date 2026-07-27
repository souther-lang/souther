package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum may have a sum as a case — spec 8.3's model of who bears a cost, where the company's own
 * share is itself one of three ways of paying. The derived codecs used to reject that: a case had to
 * be a product or a unit, so the spec's own model would not compile.
 */
class CompileNestedSumTest {

    private static final String MODULE = """
            module demo

            data Reimbursement
            data Advance
            data CorporateCard
            data Counterparty
            data OwnCompany = Reimbursement | Advance | CorporateCard
            data CostBearer = OwnCompany | Counterparty
            """;

    private BytesClassLoader loader() {
        return new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
    }

    /**
     * The derived codec dispatches over the leaves, so a nested case is tagged directly. Tagging
     * the direct case instead put two levels on one "type" key: the encoder wrote
     * {@code {type: OwnCompany}}, which lost the leaf and which the decoder then rejected.
     */
    @Test
    void aLeafOfANestedSumIsTaggedDirectly() throws Exception {
        BytesClassLoader loader = loader();
        Object v = Codecs.decoded(loader, "demo.CostBearer", Map.of("type", "Reimbursement"));
        assertInstanceOf(loader.loadClass("demo.Reimbursement"), v);
    }

    @Test
    void aNestedSumRoundTrips() throws Exception {
        BytesClassLoader loader = loader();

        java.lang.reflect.Constructor<?> c = loader.loadClass("demo.Advance").getDeclaredConstructors()[0];
        c.setAccessible(true);
        Object advance = c.newInstance();

        Object back = Codecs.decoded(loader, "demo.CostBearer",
                Codecs.encode(loader, "demo.CostBearer", advance));
        assertInstanceOf(loader.loadClass("demo.Advance"), back, "decode(encode(v)) == v (spec 11.3)");
    }

    @Test
    void aDirectCaseOfTheOuterSumStillDecodes() throws Exception {
        BytesClassLoader loader = loader();
        Object v = Codecs.decoded(loader, "demo.CostBearer", Map.of("type", "Counterparty"));
        assertInstanceOf(loader.loadClass("demo.Counterparty"), v);
    }

    /**
     * The nested sum is a case of the outer one, so its class carries the outer interface — and by
     * inheritance so does every leaf under it. Without that the two halves of the model disagree:
     * the checker folds a nested sum to its leaves and accepts a {@code Reimbursement} where a
     * {@code CostBearer} is expected, the derived codec dispatches over those same leaves, and the
     * JVM then holds a {@code Reimbursement} that is not a {@code CostBearer} (issue #143).
     */
    @Test
    void aNestedSumIsASubtypeOfTheSumItIsACaseOf() throws Exception {
        BytesClassLoader loader = loader();
        Class<?> outer = loader.loadClass("demo.CostBearer");

        assertTrue(outer.isAssignableFrom(loader.loadClass("demo.OwnCompany")),
                "the nested sum implements the sum that names it as a case");
        assertTrue(outer.isAssignableFrom(loader.loadClass("demo.Reimbursement")),
                "and so a leaf under it is one too");
        assertEquals(Set.of(loader.loadClass("demo.OwnCompany"), loader.loadClass("demo.Counterparty")),
                Set.of(outer.getPermittedSubclasses()),
                "a Java switch over the outer sum can name both of its cases");
    }

    /**
     * What the sealed hierarchy is for: a Java {@code switch} over the outer sum names its two cases
     * and nothing else, and a leaf of the nested one arrives at the nested arm. javac accepted the
     * source before the fix too — one interface type is never provably unrelated to another, and
     * exhaustiveness is read off the permits list, which already named both — but no leaf could be
     * handed to it, which is where it went wrong.
     */
    @Test
    void aLeafReachesTheNestedArmOfAJavaSwitch() throws Exception {
        Map<String, byte[]> classes = new java.util.HashMap<>(Compiler.compile(MODULE));
        classes.put("demo.ReadBearer", Subclasses.compile(classes, "demo.ReadBearer", """
                package demo;
                public final class ReadBearer {
                    public static String name(CostBearer v) {
                        return switch (v) {
                            case OwnCompany own -> "own";
                            case Counterparty other -> "other";
                        };
                    }
                }
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        java.lang.reflect.Constructor<?> c = loader.loadClass("demo.Reimbursement")
                .getDeclaredConstructors()[0];
        c.setAccessible(true);

        assertEquals("own", loader.loadClass("demo.ReadBearer")
                .getMethod("name", loader.loadClass("demo.CostBearer"))
                .invoke(null, c.newInstance()));
    }

    /**
     * The round trip the mismatch broke: a field typed as the outer sum puts a checkcast on the
     * decoder's own output, so the encoder wrote a value its decoder could not read back.
     */
    @Test
    void aFieldTypedAsTheOuterSumReadsBackWhatItWrote() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE + """
                data Expense = { bearer: CostBearer }
                """), getClass().getClassLoader());

        Object written = Codecs.decoded(loader, "demo.Expense",
                Map.of("bearer", Map.of("type", "Reimbursement")));

        assertInstanceOf(loader.loadClass("demo.Expense"), written);
        assertEquals(Map.of("bearer", Map.of("type", "Reimbursement")),
                Codecs.encode(loader, "demo.Expense", written));
    }

    @Test
    void theOuterAndInnerSumAgreeOnTheTag() throws Exception {
        BytesClassLoader loader = loader();

        java.lang.reflect.Constructor<?> c = loader.loadClass("demo.Reimbursement")
                .getDeclaredConstructors()[0];
        c.setAccessible(true);
        Object reimbursement = c.newInstance();

        assertEquals("Reimbursement",
                ((Map<?, ?>) Codecs.encode(loader, "demo.CostBearer", reimbursement)).get("type"));
        assertEquals("Reimbursement",
                ((Map<?, ?>) Codecs.encode(loader, "demo.OwnCompany", reimbursement)).get("type"),
                "both levels tag the leaf, so a value encoded at one decodes at the other");
    }
}
