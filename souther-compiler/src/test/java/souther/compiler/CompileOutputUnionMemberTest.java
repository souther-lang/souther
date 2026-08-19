package souther.compiler;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior's output union may name. A member is a type a {@code match} arm can name: one of
 * the primitives, or a named data type declared here or imported. A member this module declared is
 * the union's case itself; any other — a primitive, an imported type — reaches Java through a
 * generated wrapper case, since neither a JDK class nor a class another module already emitted can
 * implement an interface declared here.
 */
class CompileOutputUnionMemberTest {

    @Test
    void aPrimitiveIsAMemberAndReachesJavaWrapped() throws Exception {
        Map<String, byte[]> classes = Compiler.compile("""
                module m exposing ( NoAnswer, half )
                data NoAnswer
                behavior half : (n: Int) -> Int | NoAnswer
                let half (n) = if n >= 0 then n / 2 else NoAnswer
                """);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> union = loader.loadClass(Emitted.result("m", "half"));
        assertEquals(List.of(loader.loadClass(Emitted.bridgeCase("m", TypeSymbol.primitive("Int"))), loader.loadClass("m.NoAnswer")),
                Arrays.asList(union.getPermittedSubclasses()),
                "the primitive joins the union as a wrapper, the local case as itself");

        Object answered = Codecs.apply(loader.loadClass("m.Half").getMethod("of").invoke(null), 7L);
        assertEquals(Emitted.bridgeCase("m", TypeSymbol.primitive("Int")), answered.getClass().getName());
        assertEquals(3L, answered.getClass().getMethod("value").invoke(answered));
    }

    @Test
    void anImportedTypeIsAMemberAndReachesJavaWrapped() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                    invariant value >= 0
                """, """
                module down exposing ( NothingOwed, owed )
                import up ( Yen )
                data NothingOwed
                behavior owed : (a: Yen, b: Yen) -> Yen | NothingOwed
                    constructs Yen
                let owed (a, b) = if a.value >= b.value then Yen(a.value - b.value) else NothingOwed
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> union = loader.loadClass(Emitted.result("down", "owed"));
        assertEquals(List.of(loader.loadClass("down.NothingOwed"), loader.loadClass(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))))),
                Arrays.asList(union.getPermittedSubclasses()));
        assertTrue(union.isAssignableFrom(loader.loadClass(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))))));
    }

    @Test
    void aCollectionCannotBeAMember() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m
                data NoOrders
                data Order = { id: String }
                behavior list : (n: Int) -> List<Order> | NoOrders
                let list (n) = NoOrders
                """));
        assertTrue(e.getMessage().contains("List"), e.getMessage());
    }

    @Test
    void twoMembersOfTheSameNameAreRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module up exposing ( Yen )
                        data Yen = Int
                        """, """
                        module down
                        data Yen = String
                        behavior pick : (n: Int) -> up.Yen | Yen
                        """)));
        assertTrue(e.getMessage().contains("`Yen` is written for two types in one union"), e.getMessage());
    }

    /** The check is on the effective members: a named sum contributes its leaves, and a leaf is what
     * an arm names and what the discriminator carries. */
    @Test
    void aLeafOfAnImportedSumClashingWithALocalTypeIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module up exposing ( Payment, Yen, Card )
                        data Payment = Yen | Card
                        data Yen = Int
                        data Card = { number: String }
                        """, """
                        module down
                        import up ( Payment )
                        data Yen = String
                        behavior pay : (n: Int) -> Payment | Yen
                        """)));
        assertTrue(e.getMessage().contains("`Yen` is written for two types in one union"), e.getMessage());
    }

    @Test
    void twoImportedSumsSharingALeafNameAreRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module a exposing ( Outcome, Yen, Refused )
                        data Outcome = Yen | Refused
                        data Yen = Int
                        data Refused
                        """, """
                        module b exposing ( Verdict, Yen, Denied )
                        data Verdict = Yen | Denied
                        data Yen = String
                        data Denied
                        """, """
                        module down
                        import a ( Outcome )
                        import b ( Verdict )
                        behavior settle : (n: Int) -> Outcome | Verdict
                        """)));
        assertTrue(e.getMessage().contains("`Yen` is written for two types in one union"), e.getMessage());
    }

    /**
     * A value answered by one behavior, opened by another and answered again. Each behavior's return
     * puts the value into its own module's bridge case and each call takes it out, so what comes back
     * holds the value itself and not another bridge case. The intermediate module is a third one, so
     * the two bridge cases are different classes and a value that skipped a conversion would arrive
     * as the wrong one rather than merely nested.
     */
    @Test
    void aValueAnsweredOpenedAndAnsweredAgainIsNotWrappedTwice() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module money exposing ( Yen )
                data Yen = Int
                """, """
                module up exposing ( NoCharge, charge )
                import money ( Yen )
                data NoCharge
                behavior charge : (a: Yen) -> Yen | NoCharge
                let charge (a) = if a.value > 0 then a else NoCharge
                """, """
                module down exposing ( Free, bill )
                import money ( Yen )
                import up ( NoCharge, charge )
                data Free
                behavior bill : (a: Yen) -> Yen | Free
                let bill (a) =
                    match charge(a) with
                    | Yen as y  -> y
                    | NoCharge  -> Free
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object yen = Codecs.decoded(loader, "money.Yen", 500L);
        Object bill = loader.loadClass("down.Bill").getMethod("of").invoke(null);

        Object answered = Codecs.apply(bill, yen);
        assertEquals(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))), answered.getClass().getName(),
                "the answer is a member of this behavior's union, not of the one it called");
        Object held = answered.getClass().getMethod("value").invoke(answered);
        assertEquals("money.Yen", held.getClass().getName(),
                "the bridge case holds the value, not another bridge case");
        assertEquals(yen, held);

        Object refused = Codecs.apply(bill, Codecs.decoded(loader, "money.Yen", 0L));
        assertEquals("down.Free", refused.getClass().getName(),
                "a member this module declared is the case itself, unwrapped");
    }

    /** One bridge case per non-local member per module, carrying every result union it belongs to —
     * the rule a local case class already follows. */
    @Test
    void oneBridgeCaseServesEveryBehaviorThatAnswersWithTheSameImportedType() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                """, """
                module down exposing ( NothingOwed, NoRefund, owed, refund )
                import up ( Yen )
                data NothingOwed
                data NoRefund
                behavior owed : (a: Yen) -> Yen | NothingOwed
                let owed (a) = if a.value > 0 then a else NothingOwed
                behavior refund : (a: Yen) -> Yen | NoRefund
                let refund (a) = if a.value > 0 then a else NoRefund
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> bridge = loader.loadClass(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))));
        assertEquals(List.of(loader.loadClass(Emitted.result("down", "owed")), loader.loadClass(Emitted.result("down", "refund"))),
                Arrays.asList(bridge.getInterfaces()),
                "one bridge case, carrying both unions it is a member of");
    }

    /** An {@code example} row on such a behavior. The row writes the Souther value — the bridge case
     * is not a name this source has — so the verifier reads it out of the answer before comparing. */
    @Test
    void anExampleRowNamesTheValueAndNotItsBridgeCase() throws Exception {
        Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                """, """
                module down exposing ( NothingOwed, owed )
                import up ( Yen )
                data NothingOwed
                behavior owed : (a: Yen, b: Yen) -> Yen | NothingOwed
                    constructs Yen
                let owed (a, b) = if a.value >= b.value then Yen(a.value - b.value) else NothingOwed
                example owed
                    | "what is left after paying part of it" :
                        (Yen(300), Yen(100)) -> Yen(200)
                    | "paying more than is owed leaves nothing owed" :
                        (Yen(100), Yen(300)) -> NothingOwed
                """));
    }

    /** A primitive member the same way: the row writes the number. */
    @Test
    void anExampleRowNamesAPrimitiveMember() throws Exception {
        Compiler.compile("""
                module m exposing ( NoAnswer, half )
                data NoAnswer
                behavior half : (n: Int) -> Int | NoAnswer
                let half (n) = if n >= 0 then n / 2 else NoAnswer
                example half
                    | "half of seven, rounded down" :
                        (7) -> 3
                    | "a negative number has no half to answer with" :
                        (-1) -> NoAnswer
                """);
    }

    /**
     * Belonging to a union does not change a member's external representation. The bridge case
     * carries no codec of its own — a consumer takes the value out and uses the codec the member
     * itself has, which is the one it would have anywhere else.
     */
    @Test
    void beingAUnionMemberLeavesTheMembersExternalRepresentationAlone() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                """, """
                module down exposing ( NothingOwed, owed )
                import up ( Yen )
                data NothingOwed
                behavior owed : (a: Yen) -> Yen | NothingOwed
                let owed (a) = if a.value > 0 then a else NothingOwed
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> bridge = loader.loadClass(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))));
        for (String factory : List.of("encoder", "decoder")) {
            assertThrows(NoSuchMethodException.class, () -> bridge.getMethod(factory),
                    "a bridge case is a JVM form, not a type with an external representation");
        }
        Object answered = Codecs.apply(loader.loadClass("down.Owed").getMethod("of").invoke(null),
                Codecs.decoded(loader, "up.Yen", 500L));
        Object held = answered.getClass().getMethod("value").invoke(answered);
        assertEquals(500L, Codecs.encode(loader, "up.Yen", held),
                "the member encodes as it does on its own — bare, since a newtype outside a sum is bare");
    }

    /**
     * A Java implementation of an injected behavior whose output union has a bridged member. It has
     * to answer with a member of the union, so the base has to hand it the bridge case the way it
     * hands it every other case it may build (spec §jvm-anonymous-union).
     */
    @Test
    void anInjectedBehaviorCanAnswerWithABridgedMember() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                """, """
                module down exposing ( NothingOwed, owed )
                import up ( Yen )
                data NothingOwed
                behavior owed : (a: Yen) -> Yen | NothingOwed
                    constructs Yen
                """));
        byte[] impl = Subclasses.compile(classes, "consumer.HalfOwed", """
                package consumer;
                import up.Yen;
                import down.NothingOwed;
                import down.Owed;
                import down.OwedResult;
                import down.YenCase;
                public final class HalfOwed extends Owed {
                    @Override public OwedResult apply(Yen a) {
                        return a.value() > 0 ? new YenCase(Yen(a.value() / 2)) : NothingOwed();
                    }
                }
                """);
        Map<String, byte[]> all = new LinkedHashMap<>(classes);
        all.put("consumer.HalfOwed", impl);
        BytesClassLoader loader = new BytesClassLoader(all, getClass().getClassLoader());
        Object behavior = loader.loadClass("consumer.HalfOwed").getConstructor().newInstance();
        Object answered = Codecs.apply(behavior, Codecs.decoded(loader, "up.Yen", 500L));
        assertEquals(Emitted.bridgeCase("down", TypeSymbols.declared(new TypeKey("up", "Yen"))), answered.getClass().getName());
        Object held = answered.getClass().getMethod("value").invoke(answered);
        assertEquals(250L, held.getClass().getMethod("value").invoke(held));
    }

    /**
     * A bridge case takes a class name in this module, so it is subject to the rule every other name
     * this module emits is subject to. `+YenCase+` is a name a model may well have declared, and so
     * are `+IntCase+` and `+DateCase+`, so the collision is reported rather than the names reserved.
     */
    @Test
    void aBridgeCaseCollidingWithALocalDataTypeIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module up exposing ( Yen )
                        data Yen = Int
                        """, """
                        module down exposing ( YenCase, NothingOwed, owed )
                        import up ( Yen )
                        data YenCase = String
                        data NothingOwed
                        behavior owed : (a: Yen) -> Yen | NothingOwed
                        let owed (a) = if a.value > 0 then a else NothingOwed
                        """)));
        assertTrue(e.getMessage().contains("`YenCase`"), e.getMessage());
    }

    @Test
    void aPrimitiveBridgeCaseCollidingWithALocalDataTypeIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m exposing ( IntCase, NoAnswer, half )
                data IntCase = String
                data NoAnswer
                behavior half : (n: Int) -> Int | NoAnswer
                let half (n) = if n >= 0 then n / 2 else NoAnswer
                """));
        assertTrue(e.getMessage().contains("`IntCase`"), e.getMessage());
    }

    /** A behavior capitalizes into a class name too (spec §jvm-behavior), and it is the same table. */
    @Test
    void aBridgeCaseCollidingWithABehaviorsClassIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m exposing ( NoAnswer, half, intCase )
                data NoAnswer
                behavior intCase : (n: Int) -> Int
                let intCase (n) = n
                behavior half : (n: Int) -> Int | NoAnswer
                let half (n) = if n >= 0 then n / 2 else NoAnswer
                """));
        assertTrue(e.getMessage().contains("`IntCase`"), e.getMessage());
    }

    /**
     * Two types of one spelling from two modules. The member-name rule refuses them within a union;
     * here they are members of two different unions of this module, and both want one bridge case.
     */
    @Test
    void twoMembersOfOneSpellingInDifferentUnionsAreRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module a exposing ( Yen )
                        data Yen = Int
                        """, """
                        module b exposing ( Yen )
                        data Yen = String
                        """, """
                        module down exposing ( NoneA, NoneB, first, second )
                        data NoneA
                        data NoneB
                        behavior first : (n: Int) -> a.Yen | NoneA
                        behavior second : (n: Int) -> b.Yen | NoneB
                        """)));
        assertTrue(e.getMessage().contains("`YenCase`"), e.getMessage());
    }
}
