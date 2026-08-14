package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which case a behavior answered with is read off the value, and the value carries its module.
 *
 * <p>A row's answer arrives as a live value of the class it was generated as, and that class names
 * the module that declares it. Asking instead what this module means by the class's simple name
 * answers for whatever this module has under that spelling: nothing, where the type is reached
 * through an alias, and the wrong declaration where the reading module spells something else the
 * same.
 *
 * <p>Two modules, because that is where the two ways of asking come apart, and the same model twice
 * — once reached by an alias and once by a bare import — because the answer must not depend on how
 * the reading module spells what it imports. Both rows hold in both, so a difference here is a
 * difference in what was recorded about rows that passed.
 */
class AnAnsweredCaseIsReadOffTheValueAndNotResolvedHereTest {

    private static final String LIB = """
            module lib exposing ( Yes, No, Answer )

            data Yes
            data No
            data Answer = Yes | No
            """;

    /** Reaches the type through an alias, so no bare name of this module spells it. */
    private static final String THROUGH_AN_ALIAS = """
            module viaalias exposing ( In, f )

            import lib as up

            data In = { n: Int }

            behavior f : (i: In) -> up.Answer constructs up.Yes, up.No
            let f (i) = if i.n > 0 then up.Yes else up.No

            example f
                | "yes" : (In { n = 1 }) -> up.Yes
                | "no"  : (In { n = 0 }) -> up.No
            """;

    /** The same model, spelled bare: the control that says the alias is the only difference. */
    private static final String SPELLED_BARE = """
            module viabare exposing ( In, g )

            import lib ( Answer, Yes, No )

            data In = { n: Int }

            behavior g : (i: In) -> Answer constructs Yes, No
            let g (i) = if i.n > 0 then Yes else No

            example g
                | "yes" : (In { n = 1 }) -> Yes
                | "no"  : (In { n = 0 }) -> No
            """;

    /**
     * Reaches the type through an alias and declares something else of the spelling its cases carry.
     * The lookup that missed above answers here — with this module's declaration, which the rows
     * never mention and no value of theirs is.
     */
    private static final String SPELLS_ITS_OWN = """
            module shadows exposing ( In, Yes, h )

            import lib as up

            data In = { n: Int }
            data Yes = { irrelevant: String }

            behavior h : (i: In) -> up.Answer constructs up.Yes, up.No
            let h (i) = if i.n > 0 then up.Yes else up.No

            example h
                | "yes" : (In { n = 1 }) -> up.Yes
                | "no"  : (In { n = 0 }) -> up.No
            """;

    private static List<TypeName> armsAnsweredIn(String module, String source) {
        Compilation compilation = Compilation.ofSources(List.of(LIB, source), ModulePath.EMPTY);
        compilation.answerEverything();
        String sourceId = compilation.exampleSourcesOf(module).get(0);
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples(module, sourceId, Output.CoverageMode.NONE))
                .value().rows();
        assertEquals(2, rows.size(), rows.toString());
        return rows.stream().map(RowOutcome::resultArm).toList();
    }

    @Test
    void aModuleReachingTheTypeThroughAnAliasObservesTheCasesItsRowsAnswerWith() {
        assertEquals(List.of(TypeSymbols.declared(new TypeKey("lib", "Yes")), TypeSymbols.declared(new TypeKey("lib", "No"))),
                armsAnsweredIn("viaalias", THROUGH_AN_ALIAS),
                "the case a row answered with is the one the value is, whatever this module calls it");
    }

    /**
     * The stronger of the two. A miss says the reading failed and can be seen; an answer of the
     * wrong declaration is a reading that succeeded and means something else, and nothing in the
     * report says which of the two `Yes` a row confirmed.
     */
    @Test
    void aModuleThatSpellsSomethingElseTheSameObservesTheCasesItsRowsAnswerWith() {
        assertEquals(List.of(TypeSymbols.declared(new TypeKey("lib", "Yes")), TypeSymbols.declared(new TypeKey("lib", "No"))),
                armsAnsweredIn("shadows", SPELLS_ITS_OWN),
                "the case a row answered with is the one the value is, and this module's `Yes` is"
                        + " not a value any of these rows produced");
    }

    @Test
    void spellingTheImportBareAnswersTheSame() {
        assertEquals(armsAnsweredIn("viabare", SPELLED_BARE),
                armsAnsweredIn("viaalias", THROUGH_AN_ALIAS),
                "how the reading module reaches the type is not part of what its rows observed");
    }
}
