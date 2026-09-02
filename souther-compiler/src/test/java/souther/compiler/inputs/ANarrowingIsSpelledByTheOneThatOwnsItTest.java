package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Shape;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A narrowing is spelled where narrowings are owned, and nowhere else.
 *
 * <p>Two vocabularies say which narrowing a place carries. What a position's type divides into is
 * {@link Case}, read by {@link Distinctions}; which of those divisions a written arm selected is
 * {@link CaseSelector}, decided by the checker. Both settle a narrowing on their own, so both have
 * a way in here — and what may not have one is a value that settles less than a narrowing. A name
 * is such a value: an optional's present carrier and a case of a sum declared as {@code Some} are
 * written the same word, so a narrowing built from the name is one of the two chosen by whoever
 * built it.
 *
 * <p>That is not a hypothetical. {@code Refinement.sumCase(TypeSymbol)} was the second way in, and
 * the reading of a {@code match} arm used it: every path a body wrote through {@code Some v} came
 * out carrying a sum's case where the reading of the position carried a presence. The two spell
 * {@code x@Some} alike and are not equal, so those paths were positions nothing else in this
 * compiler names — silence wherever a reader shrugs at a path it cannot find, and an internal error
 * in the one place that refuses (#1252).
 *
 * <p>What holds the rule is that the variants have no constructor a caller can reach and that the
 * two ways in take the two values that determine a narrowing. What holds the correspondence is
 * {@link #twoVocabulariesAnswerOneNarrowing}, below: exhaustiveness stops a variant being added
 * without an answer, and only a comparison stops an existing one being answered wrongly.
 */
class ANarrowingIsSpelledByTheOneThatOwnsItTest {

    @Test
    void aNarrowingHasNoConstructorAReaderCanReach() {
        for (Class<?> variant : new Class<?>[] {Refinement.SumCase.class, Refinement.Presence.class}) {
            for (Constructor<?> each : variant.getDeclaredConstructors()) {
                assertTrue(Modifier.isPrivate(each.getModifiers()),
                        "a reader could spell a narrowing of its own: " + each);
            }
            assertEquals(0, variant.getConstructors().length,
                    () -> "and none of " + variant.getSimpleName()
                            + " is reachable by reflection either");
        }
    }

    /**
     * And every way in takes a value that already settles which narrowing it is.
     *
     * <p>Named rather than counted. A count is tripped by a private helper, which is nobody's way
     * in, and the reading of it that fits is to raise the number — which lets a way in be added
     * later with nothing having said so. What is checked beside the names is what each of them
     * takes: a way in whose parameter is a name, a string or a list of case types is one that
     * cannot tell the two narrowings apart, whatever it is called.
     */
    @Test
    void everyWayInTakesAValueThatSettlesTheNarrowing() {
        List<java.lang.reflect.Method> ways =
                java.util.Arrays.stream(Refinement.class.getDeclaredMethods())
                        .filter(each -> Modifier.isStatic(each.getModifiers())
                                && !Modifier.isPrivate(each.getModifiers()))
                        .toList();
        assertEquals(java.util.Set.of("of"),
                ways.stream().map(java.lang.reflect.Method::getName)
                        .collect(java.util.stream.Collectors.toSet()),
                "a way to spell a narrowing that is not `of` is a decision, not an accident");
        assertEquals(java.util.Set.of(Case.class, CaseSelector.class),
                ways.stream().map(each -> each.getParameterTypes()[0])
                        .collect(java.util.stream.Collectors.toSet()),
                "a narrowing is made from what a position divides into or from what an arm"
                        + " selected, and from nothing that settles less than either");
    }

    /**
     * The two vocabularies answer one narrowing, shape by shape.
     *
     * <p>The correspondence itself, and the reason the exhaustive {@code switch}es are not the whole
     * of the rule. Nothing stops {@code OptionPresent} being answered with {@code Presence(false)}:
     * every arm would be covered, every reading would compile, and an optional's arms would swap
     * which position they wrote at. So each division a type states is matched here against the
     * selector a pattern selecting it carries.
     *
     * <p>Read off a compiled model rather than written out, so that what the checker actually builds
     * for {@code Some} is what is compared — a selector written here by hand would agree with
     * whatever this test thought the checker does.
     */
    @Test
    void twoVocabulariesAnswerOneNarrowing() {
        Read read = read("""
                module m

                data Empty
                data Held = { least: Int }
                data Slot = Empty | Held
                data Box = { slot: Slot, tag: Int? }
                data Ack = { at: String }

                behavior open : (b: Box) -> Ack
                """);

        assertEquals(List.of("Empty", "Held"), spelledCases(read, "slot"),
                "the sum states its cases");
        assertEquals(List.of("None", "Some"), spelledCases(read, "tag"),
                "and the optional states whether it holds anything");

        for (Case each : distinctionsAt(read, "slot")) {
            Case.SumCase one = (Case.SumCase) each;
            assertEquals(Refinement.of(each), Refinement.of(CaseSelector.direct(one.leaf())),
                    () -> "a case of a sum is one narrowing, read either way: " + one.leaf());
        }
        Type held = elementOf(read, "tag");
        assertEquals(Refinement.of(new Case.Presence(true)),
                Refinement.of(CaseSelector.optionPresent(held)),
                "an optional holding something is one narrowing, read either way");
        assertEquals(Refinement.of(new Case.Presence(false)),
                Refinement.of(CaseSelector.optionAbsent()),
                "and so is an optional holding nothing");
    }

    /**
     * And the two are told apart, which is what makes the correspondence load-bearing.
     *
     * <p>A presence and a case of a sum are unequal however they are spelled, so a reader that
     * built one where the other belongs writes at a position nothing else reaches. Were they equal
     * instead, the mistake would be invisible and this correspondence would say nothing.
     */
    @Test
    void aPresenceIsNotACaseOfASumHoweverItIsWritten() {
        Refinement declaredSome = Refinement.of(CaseSelector.direct(
                souther.compiler.types.TypeSymbols.declared(
                        new souther.compiler.types.TypeKey("m", "Some"))));

        assertEquals("Some", declaredSome.spelled());
        assertEquals("Some", Refinement.of(new Case.Presence(true)).spelled());
        assertNotEquals(Refinement.of(new Case.Presence(true)), declaredSome,
                "two places written `@Some` are two places where one is an optional's carrier");
        assertNotEquals(declaredSome.discriminated(),
                Refinement.of(new Case.Presence(true)).discriminated(),
                "and a message about this compiler says which of them it holds");
    }

    /**
     * A narrowing is what it narrows to, and not which object it is.
     *
     * <p>Load-bearing rather than tidy. Every reader deciding whether two requirements hold together
     * does it by equality ({@link Requirements#merge}), and every branch of a position is found by
     * comparing the narrowing it carries — so an identity comparison would have no two narrowings
     * ever agree, which reads as a model whose cases are all incompatible.
     */
    @Test
    void twoNarrowingsToTheSameThingAreOne() {
        assertEquals(anInt(), anInt());
        assertEquals(anInt().hashCode(), anInt().hashCode());
        assertNotEquals(anInt(), Refinement.of(CaseSelector.direct(TypeSymbol.primitive("Bool"))));

        assertEquals(Refinement.of(new Case.Presence(true)), Refinement.of(new Case.Presence(true)));
        assertNotEquals(Refinement.of(new Case.Presence(true)),
                Refinement.of(new Case.Presence(false)));
        assertFalse(Refinement.of(new Case.Presence(true)).equals(anInt()),
                "and a presence is not a case of a sum");
    }

    private static Refinement anInt() {
        return Refinement.of(CaseSelector.direct(TypeSymbol.primitive("Int")));
    }

    /** What the type at {@code field} of the parameter divides into. */
    private static List<Case> distinctionsAt(Read read, String field) {
        return Distinctions.ofType(
                TypeView.of(read.inputs.at(TermPath.of("b").then(field)).view().declared(),
                        read.symbols),
                read.symbols);
    }

    private static List<String> spelledCases(Read read, String field) {
        List<String> out = new ArrayList<>();
        for (Case each : distinctionsAt(read, field)) {
            out.add(Refinement.of(each).spelled());
        }
        return out;
    }

    /** What the optional at {@code field} holds, which is what its present carrier is written for. */
    private static Type elementOf(Read read, String field) {
        TypeView view = TypeView.of(
                read.inputs.at(TermPath.of("b").then(field)).view().declared(), read.symbols);
        return ((Shape.Optional) view.shape()).element();
    }

    private record Read(InputDomain inputs, Symbols symbols) {}

    private static Read read(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("open")).findFirst().orElseThrow();
        return new Read(
                InputDomain.of(spec, sigs.get("open"), symbols, ReadAs.THE_COMPILATION_DOES),
                symbols);
    }
}
