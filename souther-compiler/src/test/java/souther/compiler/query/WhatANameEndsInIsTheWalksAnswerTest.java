package souther.compiler.query;

import souther.compiler.check.NewtypeInners;
import souther.compiler.check.TypeOps;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name is left as once every name is off, answered by the compilation for a module at a
 * time, is what the walk over the names answers one name at a time.
 *
 * <p>The walk stops on the first name it has already worn, so where the names come back round the
 * answer depends on where the walk began: a name on the cycle is its own terminal, and a name before
 * the cycle ends at the name it enters it by. The module's answer has to say the same for each name.
 */
class WhatANameEndsInIsTheWalksAnswerTest {

    private static final String BENEATH = """
            module shop.beneath exposing ( Cents, Level, Stage, Sized, Note )

            data Cents = Int

            data Level = Cents

            data Stage = Opening | Closing

            data Opening

            data Closing

            data Sized = { width: Int }

            data Note = Sized
            """;

    private static final String ABOVE = """
            module shop.above exposing ( Price, Rank, Phase, Shape, X, A, B, BeforeA, BeforeB )

            import shop.beneath ( Cents, Level, Stage, Sized, Note )

            data Rank = Level

            data Price = Rank

            data Phase = Stage

            data Shape = Note

            data Plain = { at: Int }

            data X = X

            data A = B

            data B = A

            data BeforeA = A

            data BeforeB = B
            """;

    /** Every name either module declares ends where the walk from it ends. */
    @Test
    void everyNameEndsWhereTheWalkFromItEnds() {
        Compilation c = compiling();
        NewtypeInners inners = Shapes.newtypeInners(c.db());

        List<String> compared = new ArrayList<>();
        for (TypeKey named : declaredIn(c, "shop.beneath", "shop.above")) {
            Type type = Type.ref(TypeSymbols.declared(named));
            assertEquals(TypeOps.newtypeSpine(type, inners).terminal(), inners.terminal(type),
                    "what " + named + " is left as once the names are off");
            compared.add(named.name());
        }
        assertTrue(compared.containsAll(List.of("X", "A", "B", "BeforeA", "BeforeB", "Price", "Plain")),
                "the cycles and the chains were among what was compared: " + compared);
    }

    /** Said apart from the walk, so the two agreeing is not both being wrong the same way. */
    @Test
    void aNameOnACycleIsItsOwnTerminalAndANameBeforeOneEndsWhereItEntersIt() {
        Compilation c = compiling();
        NewtypeInners inners = Shapes.newtypeInners(c.db());

        assertEquals(above("X"), inners.terminal(above("X")));
        assertEquals(above("A"), inners.terminal(above("A")));
        assertEquals(above("B"), inners.terminal(above("B")));
        assertEquals(above("A"), inners.terminal(above("BeforeA")));
        assertEquals(above("B"), inners.terminal(above("BeforeB")));
        assertEquals(Type.INT, inners.terminal(above("Price")));
        assertEquals(beneath("Sized"), inners.terminal(above("Shape")));
        assertEquals(above("Plain"), inners.terminal(above("Plain")));
    }

    /**
     * A module asks of the names it wraps and of nothing beneath them.
     *
     * <p>{@code Price} ends three names down and two of them are in the module beneath, and the
     * answer for this module reads the beneath module's answer for {@code Level} — its own chain,
     * already followed there — and not the names under {@code Level}.
     */
    @Test
    void aModuleAsksOfTheNamesItWrapsAndOfNothingBeneathThem() {
        Compilation c = compiling();
        c.db().ask(new Shapes.NewtypeTerminals("shop.above"));

        Set<Key<?>> elsewhere = c.db().dependenciesOf(new Shapes.NewtypeTerminals("shop.above")).stream()
                .filter(each -> each instanceof Shapes.NewtypeTerminalOf)
                .collect(Collectors.toSet());
        assertEquals(Set.of(
                        new Shapes.NewtypeTerminalOf(new TypeKey("shop.beneath", "Level")),
                        new Shapes.NewtypeTerminalOf(new TypeKey("shop.beneath", "Stage")),
                        new Shapes.NewtypeTerminalOf(new TypeKey("shop.beneath", "Note"))),
                elsewhere, "what the module beneath answers, for the names this one wraps");
    }

    /**
     * Each name a module declares is read once however its chains run, so a module of names stacked
     * on each other is followed in as many steps as it has names.
     *
     * <p>In both orders: written top down, the first walk goes the whole way and every walk after it
     * is answered; written bottom up, every walk is one step onto a name already answered.
     */
    @Test
    void eachNameIsReadOnceWhicheverWayItsChainIsWritten() {
        int links = 200;
        Map<TypeKey, Type> wraps = new LinkedHashMap<>();
        wraps.put(key("T1"), Type.INT);
        for (int i = 2; i <= links; i++) {
            wraps.put(key("T" + i), Type.ref(TypeSymbols.declared(key("T" + (i - 1)))));
        }
        List<TypeKey> bottomUp = new ArrayList<>(wraps.keySet());
        List<TypeKey> topDown = bottomUp.reversed();

        for (List<TypeKey> written : List.of(bottomUp, topDown)) {
            Map<TypeKey, Integer> read = new HashMap<>();
            NewtypeInners counting = declaration -> {
                read.merge(declaration, 1, Integer::sum);
                return wraps.get(declaration);
            };
            Map<TypeKey, Type> terminals =
                    Shapes.NewtypeTerminals.within("m", written, counting, _ -> null);

            assertEquals(links, terminals.size());
            assertTrue(terminals.values().stream().allMatch(Type.INT::equals));
            assertEquals(Set.of(1), Set.copyOf(read.values()),
                    "each name read once, written " + (written == bottomUp ? "bottom up" : "top down"));
            assertEquals(links, read.size());
        }
    }

    /** And where the names come back round, each is still read once and the walk's answer kept. */
    @Test
    void aCycleIsReadOnceAndAnsweredAsTheWalkAnswersIt() {
        Map<TypeKey, Type> wraps = new LinkedHashMap<>();
        wraps.put(key("BeforeA"), ref("A"));
        wraps.put(key("A"), ref("B"));
        wraps.put(key("B"), ref("A"));
        wraps.put(key("BeforeB"), ref("B"));
        wraps.put(key("X"), ref("X"));
        Map<TypeKey, Integer> read = new HashMap<>();
        NewtypeInners counting = declaration -> {
            read.merge(declaration, 1, Integer::sum);
            return wraps.get(declaration);
        };

        Map<TypeKey, Type> terminals = Shapes.NewtypeTerminals.within(
                "m", List.copyOf(wraps.keySet()), counting, _ -> null);

        NewtypeInners walking = wraps::get;
        for (TypeKey named : wraps.keySet()) {
            assertEquals(TypeOps.newtypeSpine(ref(named.name()), walking).terminal(),
                    terminals.get(named), "what " + named.name() + " is left as");
        }
        assertEquals(Set.of(1), Set.copyOf(read.values()), "each name read once: " + read);
    }

    /** A chain that leaves the module asks once where it leaves, and not again for each name above. */
    @Test
    void aChainLeavingTheModuleAsksWhereItLeavesOnce() {
        TypeKey outside = new TypeKey("n", "Below");
        Map<TypeKey, Type> wraps = new LinkedHashMap<>();
        wraps.put(key("T1"), Type.ref(TypeSymbols.declared(outside)));
        for (int i = 2; i <= 50; i++) {
            wraps.put(key("T" + i), ref("T" + (i - 1)));
        }
        List<TypeKey> asked = new ArrayList<>();

        Map<TypeKey, Type> terminals = Shapes.NewtypeTerminals.within(
                "m", List.copyOf(wraps.keySet()).reversed(), wraps::get, named -> {
                    asked.add(named);
                    return Type.DECIMAL;
                });

        assertEquals(List.of(outside), asked);
        assertTrue(terminals.values().stream().allMatch(Type.DECIMAL::equals));
    }

    private static TypeKey key(String name) {
        return new TypeKey("m", name);
    }

    private static Type ref(String name) {
        return Type.ref(TypeSymbols.declared(key(name)));
    }

    private static Type above(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey("shop.above", name)));
    }

    private static Type beneath(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey("shop.beneath", name)));
    }

    private static List<TypeKey> declaredIn(Compilation c, String... modules) {
        List<TypeKey> declared = new ArrayList<>();
        for (String module : modules) {
            for (String name : c.db().ask(new Names.Declarations(module)).value().asDeclared()) {
                declared.add(new TypeKey(module, name));
            }
        }
        return declared;
    }

    private static Compilation compiling() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("beneath.sou", BENEATH);
        byId.put("above.sou", ABOVE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }
}
