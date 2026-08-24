package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.ResultBound;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every fact declared of the language's operations is held to what the library declares, whether or
 * not anything asks for it.
 *
 * <p>The declarations and the procedure that holds them to the library are in different places now:
 * a fact is a proposition about an operation and is declared where those are, and holding one to a
 * signature reads the library, which is the frontend's. What that arrangement can lose is the
 * reaching — bound one fact at a time as it was looked up, a fact nothing looked up was a fact
 * nothing checked, and how much of the declaration was validated depended on which consumers a
 * compilation happened to have.
 *
 * <p>So what is asked here is coverage of the declarations and not of the lookups. A test naming
 * the facts that exist today would be a second copy of the list, wrong in the same way one turn
 * later; these are asked of the source, so a fact declared tomorrow is inside them without anyone
 * adding a line.
 */
class EverySemanticDeclarationIsHeldToTheLibraryTest {

    /** Everything the language declares is visited, and the visiting is over the declarations. */
    @Test
    void theBindingIsOverTheDeclarations() {
        assertEquals(OperationFacts.declarations(),
                OperationFactBinder.bindAll(DefaultStdlib.get(), OperationFacts.declarations()),
                "what the binding visited is what is declared");
        assertTrue(!OperationFacts.declarations().isEmpty(),
                "and there is something declared for that to mean anything");
    }

    /**
     * A fact the source gains is held too, without the binding being told about it.
     *
     * <p>The whole of the contract, and the part the assertion above cannot show on its own: a
     * binding that walked a list of its own would visit exactly what is declared today and nothing
     * that arrives later. So one is added here that the library refuses, and the binding is asked
     * whether it noticed.
     */
    @Test
    void aFactTheDeclarationsGainIsHeldWithoutTheBindingBeingTold() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("Decimal", "fromInt"),
                new OperationFact.AnswersAFormOfItsArguments(
                        souther.compiler.numeric.NumericDomain.LinearForm.atom(
                                new ArgumentRef.At(7)))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained));

        assertTrue(refused.getMessage().contains("Decimal.fromInt"), refused.getMessage());
        assertTrue(refused.getMessage().contains("argument 8"),
                "the argument the added fact names, which the operation does not take: "
                        + refused.getMessage());
    }

    /**
     * What a fact says of the result is held to the library as well as what it says of an argument.
     *
     * <p>The half the tests above cannot see. Each of them adds a fact naming an argument the
     * operation does not have, so what they show is that the argument side of a proposition is held.
     * Only one primitive existed and it named an argument, so a fact about the result was held by
     * whatever its own arm remembered to write — and a form is an equation between the two ends.
     * {@code List.get(index, xs)} declared to answer the count of its first argument passes on the
     * argument side, that argument being an {@code Int}, while what it answers is an
     * {@code Option<'a>} and has no count for the equation to be about.
     */
    @Test
    void whatAFactSaysOfTheResultIsHeldToTheLibraryToo() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("List", "get"),
                new OperationFact.AnswersAFormOfItsArguments(
                        souther.compiler.numeric.NumericDomain.LinearForm.atom(
                                new ArgumentRef.At(0)))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained),
                "a form is an equation between what an operation answers and what it was given, so"
                        + " a result with no count is a result the equation is not about");

        assertTrue(refused.getMessage().contains("List.get"), refused.getMessage());
        assertTrue(refused.getMessage().contains("what"),
                "what it answers is what is wrong, and the message says so: "
                        + refused.getMessage());
    }

    /**
     * And a fact stated of the result that names no argument at all.
     *
     * <p>Beside the above because nothing else in it reaches a signature. A bound with no argument
     * to hold the result against names none, so its arm held the operation and stopped; a bound on
     * what {@code List.get} answers went through it. Two kinds were in this position —
     * {@code BoundsItsResult} and {@code IsDefinedByCases} — and both are stated of a number.
     */
    @Test
    void aFactStatedOfTheResultAndNamingNoArgumentIsHeldToo() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("List", "get"),
                new OperationFact.BoundsItsResult(new ResultBound(null, BigDecimal.ZERO,
                        Rel.GE, new ResultBound.Provided.Always()))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained),
                "a bound is stated of the number an operation answers, and List.get answers no"
                        + " number");

        assertTrue(refused.getMessage().contains("List.get"), refused.getMessage());
    }

    /**
     * A fact that names no argument is held to the library too.
     *
     * <p>What the two tests below cannot show, and the hole they left. Both of them add a fact that
     * names an argument, and holding an argument to a signature reads the library on the way — so
     * what they were showing was that <em>that kind of fact</em> reaches the library, not that
     * every declaration does. A fact naming no argument went through an arm with nothing in it and
     * was bound to nothing at all.
     *
     * <p>{@code CountsWhatItIsGiven} is one of those, and it is declared here of an operation the
     * library does not have. A binding that holds an operation only where a fact happens to name an
     * argument accepts it.
     */
    @Test
    void aFactNamingNoArgumentIsHeldToTheLibraryToo() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("List", "howManyThereAreNot"),
                new OperationFact.CountsWhatItIsGiven()));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained),
                "a fact is bound because it is declared, and not because its kind names an"
                        + " argument that happens to be read against a signature");

        assertTrue(refused.getMessage().contains("List.howManyThereAreNot"), refused.getMessage());
        assertTrue(refused.getMessage().contains("the library does not declare"),
                refused.getMessage());
    }

    /**
     * And a fact about an operation the library does not declare at all.
     *
     * <p>Beside the above because it fails one question earlier: there is no signature to read the
     * argument against, so what is wrong is the operation and not the argument.
     */
    @Test
    void aFactAboutAnOperationTheLibraryDoesNotDeclareIsRefused() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("Decimal", "fromNothingAtAll"),
                new OperationFact.AnswersAFormOfItsArguments(
                        souther.compiler.numeric.NumericDomain.LinearForm.atom(
                                new ArgumentRef.At(0)))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained));

        assertTrue(refused.getMessage().contains("the library does not declare"),
                refused.getMessage());
    }
}
