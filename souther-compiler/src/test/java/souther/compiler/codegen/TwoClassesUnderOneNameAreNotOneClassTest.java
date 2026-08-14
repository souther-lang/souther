package souther.compiler.codegen;

import souther.compiler.Emitted;
import org.junit.jupiter.api.Test;
import souther.compiler.jvm.DecoderKind;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module emits holds one class under one JVM name, and says which two things wanted it when it
 * does not.
 *
 * <p>A plain map answers a second write of a name by keeping the second and dropping the first, so the
 * compile succeeded and the artifact set was a class short — which arrived, much later, as a linkage
 * error against whatever had gone missing. What is written here is not a name but a
 * {@link GeneratedClass}, and the map from those to names is not injective: two identities that mean
 * different things can land on one class. That is where a collision exists, so that is what is keyed
 * on — and the identities are kept under the key so the report says what collided rather than only
 * that something did.
 *
 * <p>No source reaches either of these today; both pairs are refused where they are declared. This is
 * the backstop under those rules, and it is what a naming scheme changed later runs into instead of
 * the silence.
 */
class TwoClassesUnderOneNameAreNotOneClassTest {

    private static final GeneratedClass.Value QUOTE_DATA =
            new GeneratedClass.Value(TypeSymbols.declared(new TypeKey("demo", "Quote")));
    private static final GeneratedClass.BehaviorInterface QUOTE_BEHAVIOR =
            new GeneratedClass.BehaviorInterface("demo", "quote");

    @Test
    void aDataAndABehaviorThatCapitalizesOntoItAreOneClass() {
        Emissions out = new Emissions();
        out.put(QUOTE_DATA, new byte[] {1});
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.put(QUOTE_BEHAVIOR, new byte[] {2}));
        assertTrue(refused.getMessage().contains("demo.Quote"),
                "the refusal names the class both wanted: " + refused.getMessage());
        assertTrue(refused.getMessage().contains("Quote") && refused.getMessage().contains("quote"),
                "and the two identities that wanted it: " + refused.getMessage());
        assertEquals(List.of(Emitted.value("demo", "Quote")), List.copyOf(out.byBinaryName().keySet()),
                "the class already written stays the one that is written");
        assertEquals(1, out.byBinaryName().get(Emitted.value("demo", "Quote"))[0],
                "and it is not replaced on the way out");
    }

    /** Two members of one spelling from two modules, bridged into one module. Different identities —
     *  and this ABI has one name for them. */
    @Test
    void twoMembersBridgedUnderOneNameAreOneClass() {
        Emissions out = new Emissions();
        out.put(new GeneratedClass.BridgeCase("demo", TypeSymbols.declared(new TypeKey("a", "Foo"))), new byte[] {1});
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.put(new GeneratedClass.BridgeCase("demo", TypeSymbols.declared(new TypeKey("b", "Foo"))),
                        new byte[] {2}));
        assertTrue(refused.getMessage().contains("a.Foo") && refused.getMessage().contains("b.Foo"),
                "the refusal names both members: " + refused.getMessage());
    }

    /**
     * And the same pair through the other door. Writing a declaration onto a class asks for it by
     * identity, and finding something under that name is not finding that identity — the two spell
     * the same. Without this the behavior's declaration would go onto the data's class and the
     * registry would then say the class had been emitted for the behavior.
     */
    @Test
    void oneIdentityCannotRewriteAnotherThatHasTheSameName() {
        Emissions out = new Emissions();
        out.put(QUOTE_DATA, new byte[] {1});
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.rewrite(QUOTE_BEHAVIOR, bytes -> new byte[] {2}));
        assertTrue(refused.getMessage().contains("Quote") && refused.getMessage().contains("quote"),
                "the refusal names what was emitted and what asked: " + refused.getMessage());
        assertEquals(1, out.byBinaryName().get(Emitted.value("demo", "Quote"))[0],
                "and the class is not rewritten");
    }

    /** The control: the identity that was emitted may rewrite what it holds, and stays what it is. */
    @Test
    void andTheIdentityThatWasEmittedMayRewriteIt() {
        Emissions out = new Emissions();
        out.put(QUOTE_DATA, new byte[] {1});
        out.rewrite(QUOTE_DATA, bytes -> new byte[] {(byte) (bytes[0] + 1)});
        assertEquals(2, out.byBinaryName().get(Emitted.value("demo", "Quote"))[0]);
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.put(QUOTE_DATA, new byte[] {3}));
        assertTrue(refused.getMessage().contains("written twice"),
                "and a rewrite is not a second emission: " + refused.getMessage());
    }

    /** A rewrite of something nothing emitted is refused rather than becoming the emission of it. */
    @Test
    void andNothingCanBeRewrittenThatWasNeverEmitted() {
        Emissions out = new Emissions();
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.rewrite(QUOTE_DATA, bytes -> new byte[] {1}));
        assertTrue(refused.getMessage().contains("demo.Quote"), refused.getMessage());
        assertEquals(List.of(), List.copyOf(out.byBinaryName().keySet()));
    }

    /** And through the door a whole set of classes arrives by, which is how the classes compiled for
     *  escaping lambdas are added. */
    @Test
    void andSoIsOneArrivingWithOthers() {
        Emissions out = new Emissions();
        out.put(QUOTE_DATA, new byte[] {1});
        Map<GeneratedClass, byte[]> more = new LinkedHashMap<>();
        more.put(new GeneratedClass.Lambda("demo", 0), new byte[] {2});
        more.put(QUOTE_DATA, new byte[] {3});
        assertThrows(IllegalStateException.class, () -> out.putAll(more));
    }

    /** The control: identities this ABI spells apart are all written, in the order they were written
     *  in. Without it the refusals above would pass on a registry that refused everything. */
    @Test
    void andEveryOtherIdentityIsWritten() {
        Emissions out = new Emissions();
        out.put(QUOTE_DATA, new byte[] {1});
        out.putAll(Map.of(new GeneratedClass.Encoder(QUOTE_DATA), new byte[] {2}));
        out.put(new GeneratedClass.Decoder(QUOTE_DATA, DecoderKind.JSON), new byte[] {3});
        out.put(new GeneratedClass.BehaviorInterface("demo", "price"), new byte[] {4});
        assertEquals(List.of(Emitted.value("demo", "Quote"), Emitted.encoder("demo", "Quote"),
                        Emitted.decoder("demo", "Quote", DecoderKind.JSON),
                        Emitted.behaviorInterface("demo", "price")),
                List.copyOf(out.byBinaryName().keySet()));
    }
}
