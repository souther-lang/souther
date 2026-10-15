package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.DecisionArgument;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition on what a dependency answered states a proposition about that answer, and the answer
 * is the subject the decision table holds a column for.
 *
 * <p>A row stands each dependency in, so what one answers is something a row controls, as a
 * position is. The two readings of a body — what each condition means, and the table of what it
 * decides — name it through one account ({@link DecisionSubjects}), which is what this holds them to:
 * a column of the table and a part of what the fork states are one subject, or a row written for
 * one would be read against the other.
 */
class AConditionOnADependencysAnswerIsTheColumnTheTableHoldsTest {

    private static final String DECLARATIONS = """
            data Slug = String
                invariant String.length(value) >= 1
            data Draft = { title: String }
            data Found = { hash: String }
            data Missing
            behavior exists : (slug: Slug) -> Bool
            behavior lookup : (title: String) -> Found | Missing
            behavior scoreOf : (title: String) -> Int
            """;

    /**
     * A newtype built around what the dependency is asked about is the value it wraps, so the
     * question is the one asked of the input's own field.
     */
    @Test
    void aTruthOfAnAnswerIsTheTablesColumn() {
        String fork = "if exists(Slug(d.title)) then 1 else 0";
        Proposition.Truth truth = assertInstanceOf(Proposition.Truth.class, stated(fork));
        DecisionSubject.AnAnswer answer =
                assertInstanceOf(DecisionSubject.AnAnswer.class, truth.of());
        assertTrue(answer.spelled().matches("demo\\.exists\\(d\\.title\\)#\\d+"), answer.spelled());
        assertEquals(Set.of(answer), columnsOf(fork),
                "the table holds a column for the answer the fork states something of");
    }

    @Test
    void aTruthOfAnAnswerHeldAgainstOneWrittenOutIsThatTruth() {
        assertEquals(stated("if exists(Slug(d.title)) then 1 else 0").denied(),
                stated("if exists(Slug(d.title)) == false then 1 else 0"));
    }

    @Test
    void aMatchOnAnAnswerIsItsCases() {
        Proposition stated = stated("""
                if (match lookup(d.title) with
                        | Found -> true
                        | Missing -> false) then 1 else 0""");
        assertTrue(subjectsIn(stated).stream()
                        .anyMatch(each -> each instanceof DecisionSubject.AnAnswer answer
                                && answer.spelled().matches("demo\\.lookup\\(d\\.title\\)#\\d+")),
                () -> "which case the answer is is a part of what is stated: " + stated);
    }

    /**
     * A number a dependency answered is the answer, whether the call is written where it is
     * compared or a name holds it: the name is the evaluation it was given.
     */
    @Test
    void aNumberAnsweredIsTheAnswerWhereverItIsNamed() {
        assertTrue(atomsOf(stated("if scoreOf(d.title) > 5 then 1 else 0")).stream()
                .allMatch(DecisionAtom.OfAnAnswer.class::isInstance));
        assertTrue(atomsOf(stated("""
                {
                    let s = scoreOf(d.title)
                    if s > 5 then 1 else 0
                }""")).stream().allMatch(DecisionAtom.OfAnAnswer.class::isInstance));
    }

    /**
     * A dependency asked about a value the body works out is still a dependency a row stands in, and
     * its answer is the column: the row asks it the same thing however the value was worked out,
     * and the question is named by how — the title, trimmed.
     */
    @Test
    void aDependencyAskedAboutAComputedValueIsTheAnswerTheRowStandsIn() {
        String fork = "if exists(Slug(String.trim(d.title))) then 1 else 0";
        Proposition.Truth truth = assertInstanceOf(Proposition.Truth.class, stated(fork));
        DecisionSubject.AnAnswer answer =
                assertInstanceOf(DecisionSubject.AnAnswer.class, truth.of());
        assertEquals(List.of(new DecisionArgument.WorkedOut("String.trim[d.title]")),
                answer.answered().arguments());
        assertEquals(Set.of(answer), columnsOf(fork));
    }

    /**
     * Asked once for each value a list was written with, one call is as many questions as values:
     * the names they are asked by differ in the value each application handed, so none of them is
     * read as another.
     */
    @Test
    void oneCallAskedAboutEachValueWrittenOutAsksEachOfThem() {
        Proposition stated = stated("""
                if List.any(t -> exists(Slug(String.trim(t))), ["a", "b"]) then 1 else 0""");
        Set<String> asked = subjectsIn(stated).stream()
                .map(each -> ((DecisionSubject.AnAnswer) each).answered().arguments().toString())
                .collect(Collectors.toSet());
        assertEquals(Set.of("[String.trim[\"a\"]]", "[String.trim[\"b\"]]"), asked,
                () -> "each application asks its own question: " + stated);
    }

    private static Set<DecisionSubject> subjectsIn(Proposition stated) {
        return switch (stated) {
            case Proposition.Truth truth -> Set.of(truth.of());
            case Proposition.InCases cases -> Set.of(cases.of());
            case Proposition.All all -> all.parts().stream()
                    .flatMap(each -> subjectsIn(each).stream()).collect(Collectors.toSet());
            case Proposition.Any any -> any.parts().stream()
                    .flatMap(each -> subjectsIn(each).stream()).collect(Collectors.toSet());
            default -> Set.of();
        };
    }

    private static Set<Quantity> atomsOf(Proposition stated) {
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, stated);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        return affine.form().coefs().keySet();
    }

    /** The subjects the decision table holds a truth column for, over the fork written {@code
     *  fork}. */
    private static Set<DecisionSubject> columnsOf(String fork) {
        return DecisionReadings.readToTheEnd(model(fork), "f").stream()
                .flatMap(rule -> rule.consulted().keySet().stream())
                .filter(DecisionCondition.ATruth.class::isInstance)
                .map(each -> ((DecisionCondition.ATruth) each).of())
                .collect(Collectors.toSet());
    }

    /** A behavior {@code f} written {@code body}, depending on the dependencies the body asks. */
    private static String model(String body) {
        List<String> asked = List.of("exists", "lookup", "scoreOf").stream()
                .filter(each -> body.contains(each + "(")).toList();
        return "module demo\n\n" + DECLARATIONS + """

                behavior f : (d: Draft) -> Int
                    depends on %s
                let f (d, %s) =
                    %s
                """.formatted(String.join(", ", asked), String.join(", ", asked),
                body.indent(4).strip());
    }

    /** What the condition of the one fork of a body written {@code body} states. */
    private static Proposition stated(String body) {
        Compilation compilation = Compilation.ofSource(model(body), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().titleKey())
                        .toList(),
                () -> "the model compiles: " + body);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
