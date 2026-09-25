package souther.compiler.ast;

import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a module publishes, as the one place that works it out answers it (spec
 * §a-module-publishes-what-it-declares, §only-a-modules-own-declarations-are-published).
 *
 * <p>Asked of the module as parsed and not through a compile, because some of what is left out has no
 * reader that would notice today: a core module's {@code private let} is kept from callers by the
 * library's own names, so a compile answers the same whether this leaves it out or not.
 */
class AModulePublishesWhatItDeclaresTest {

    private static final String DECLARATIONS = """

            data Amount = Int

            behavior charge : (a: Amount) -> Amount
            let charge (a) = doubled(a)

            let cap = Amount(1000)
            let doubled (a: Amount) : Amount = Amount(a.value * 2)
            """;

    @Test
    void aModuleWritingNoClausePublishesEveryDeclarationItMakes() {
        Ast.Module module = CstFrontend.parse("module m\n" + DECLARATIONS, null);

        assertEquals(ExposingClause.Omitted.INSTANCE, module.exposing());
        assertEquals(Set.of("Amount", "charge", "cap", "doubled"), module.published());
    }

    @Test
    void aModuleWritingAnEmptyClausePublishesNothing() {
        Ast.Module module = CstFrontend.parse("module m exposing ()\n" + DECLARATIONS, null);

        assertEquals(new ExposingClause.Written(List.of()), module.exposing());
        assertEquals(Set.of(), module.published());
    }

    @Test
    void aModuleWritingAClausePublishesWhatItNamesAtTypeGranularity() {
        Ast.Module module = CstFrontend.parse(
                "module m exposing ( Amount.decoder, cap )\n" + DECLARATIONS, null);

        assertEquals(List.of("Amount.decoder", "cap"), module.exposing().named());
        assertEquals(Set.of("Amount", "cap"), module.published());
    }

    /** A core module's {@code private let} is the library's implementation and not its surface. */
    @Test
    void aPrivateLetIsNotPublishedByWritingNoClause() {
        Ast.Module module = CstFrontend.parse("""
                module souther.sample

                let visible (n: Int) : Int = hidden(n)
                private let hidden (n: Int) : Int = n + 1
                """, null);

        assertEquals(Set.of("visible"), module.published());
    }

    /** A value an attached file declares joins the module for its rows, and is not published. */
    @Test
    void aValueAnAttachedFileDeclaresIsNotPublishedByWritingNoClause() {
        Ast.Module written = CstFrontend.parse("module m\n" + DECLARATIONS, null);

        assertEquals(written.published(), withAnAttachedValue(written).published());
    }

    /** Naming a {@code private let} in a clause does not publish it either: the clause admits among
     *  what may be published, and a {@code private let} is not among it. */
    @Test
    void aPrivateLetNamedByTheClauseIsNotPublished() {
        Ast.Module module = CstFrontend.parse("""
                module souther.sample exposing ( visible, hidden )

                let visible (n: Int) : Int = hidden(n)
                private let hidden (n: Int) : Int = n + 1
                """, null);

        assertEquals(Set.of("visible"), module.published());
    }

    /** Nor does naming a value an attached file declares. */
    @Test
    void aValueAnAttachedFileDeclaresNamedByTheClauseIsNotPublished() {
        Ast.Module written = CstFrontend.parse(
                "module m exposing ( cap, sample )\n" + DECLARATIONS, null);

        assertEquals(Set.of("cap"), withAnAttachedValue(written).published());
    }

    /** Nor does naming what the module does not declare at all. */
    @Test
    void aNameTheModuleDoesNotDeclareIsNotPublished() {
        Ast.Module module = CstFrontend.parse(
                "module m exposing ( cap, Elsewhere )\n" + DECLARATIONS, null);

        assertEquals(Set.of("cap"), module.published());
    }

    /** {@code written} with the value {@code sample} of an attached file joined to it, as the rows'
     *  module is. */
    private static Ast.Module withAnAttachedValue(Ast.Module written) {
        Ast.Module attached = CstFrontend.parse("""
                examples for m

                let sample = Amount(5)
                """, null);
        assertEquals(List.of("sample"), attached.fns().stream().map(Ast.FnDef::name).toList(),
                "the attached file declares the value this is about");
        List<Ast.FnDef> fns = new ArrayList<>(written.fns());
        fns.addAll(attached.fns());
        return new Ast.Module(written.name(), written.exposing(), written.exposedOutputs(),
                written.imports(), written.defs(), written.behaviors(), fns, written.takenOn(),
                written.examples(), written.fakes(), written.exampleFileTarget(), written.pos());
    }
}
