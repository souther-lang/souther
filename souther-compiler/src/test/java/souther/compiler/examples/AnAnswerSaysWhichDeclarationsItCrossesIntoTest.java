package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;

import java.lang.reflect.Modifier;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An answer says which declarations the values crossing into it are read by.
 *
 * <p>A row's values are built from the module being evaluated, and they are handed to whatever
 * applies the behavior. Where that is an implementation compiled against some earlier build of the
 * module, the declarations reading them are that build's — and a run has no way to say so unless the
 * answer itself says which declarations it uses. That is what {@link Origin} is: not where the
 * classes were carried in from, which is transport, but which declarations the crossing is read by.
 *
 * <p>Asked of the answer for one behavior rather than of the answerer. A module declares behaviors
 * with a body and behaviors without one, and only the second can have an implementation supplied for
 * it, so an answerer resolving between them has an answer of each kind in one evaluation.
 */
class AnAnswerSaysWhichDeclarationsItCrossesIntoTest {

    /**
     * The compile's own answer says the declarations are the ones being evaluated.
     *
     * <p>There are not two builds here, so there is nothing to hold together — which is what
     * {@code TheCompilesOwn} says, and why a run that has only these pays nothing for the question.
     */
    @Test
    void whatACompileAppliesCrossesIntoTheDeclarationsBeingEvaluated() {
        GeneratedImplementations manifest =
                new GeneratedImplementations("example.applying", Set.of("double"));
        MemoryClassLoader empty =
                new MemoryClassLoader(Map.of(), ExampleVerifier.class.getClassLoader());

        Answerer.Answer answer = Answering.generatedHere().over(manifest, empty).of("double");

        Answerer.Answer.Something something = assertInstanceOf(Answerer.Answer.Something.class,
                answer, "the manifest says this compile implemented it");
        assertInstanceOf(TheCompilesOwn.class, something.origin(),
                "and what it applies is read by the declarations being evaluated");
    }

    /**
     * Nothing outside this package can say its answer is the compile's own.
     *
     * <p>{@code TheCompilesOwn} is not a description of an answer, it is what excuses one from being
     * held to the module being evaluated. An answerer supplied from outside a compile is written in
     * another package, and if it could name this it could excuse itself from the check by writing one
     * word. Making {@link Answerer.Answer.Something#origin} abstract keeps the question from being
     * forgotten; this keeps it from being answered falsely, and the two are different defences.
     */
    @Test
    void anAnswererWrittenElsewhereCannotSayItsAnswerIsTheCompilesOwn() {
        assertFalse(Modifier.isPublic(TheCompilesOwn.class.getModifiers()),
                "an answerer in another package cannot name it");
        assertTrue(Origin.Published.class.getModifiers() != 0
                        && Modifier.isPublic(Origin.Published.class.getModifiers()),
                "and the one it can name is the one that gets checked");
    }
}
