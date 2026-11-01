package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a condition states is made where a rule concludes it and nowhere else.
 *
 * <p>A proposition built outside this package is a statement no rule of {@link Derivation} took,
 * and nothing that walks a derivation back would find the step it came from. So the census is of who
 * builds one — a record of {@link Proposition} made, or parts joined or disjoined — and it is this
 * package and no other.
 */
class APropositionIsMadeOnlyWhereARuleConcludesItTest {

    private static final String HERE = Proposition.class.getPackageName() + ".";

    /** Whoever outside this package calls {@code method} on a proposition. */
    private static Set<String> outside(String method) {
        Set<String> out = new TreeSet<>();
        for (String each : WhatWasCompiled.callersOf(Proposition.class, method)) {
            if (!each.startsWith(HERE)) {
                out.add(each);
            }
        }
        return out;
    }

    @Test
    void noPropositionIsBuiltOutsideThisPackage() {
        assertEquals(Set.of(), outside("<init>"),
                "a proposition built here is one no rule concluded");
        assertEquals(Set.of(), outside("all"), "parts joined here are joined by no rule");
        assertEquals(Set.of(), outside("any"), "parts disjoined here are disjoined by no rule");
    }

    /**
     * A meaning is a derivation concluded, and nothing else makes one: what it states beside how it
     * was derived is what that derivation concludes, by construction rather than by every maker
     * taking care.
     */
    @Test
    void aMeaningIsMadeOnlyByConcludingItsDerivation() {
        assertEquals(Set.of(Conclusion.class.getName()),
                WhatWasCompiled.callersOf(MeaningsOfABody.Meaning.class, "<init>"),
                "a meaning made elsewhere can pair a proposition with a derivation it is not the"
                        + " conclusion of");
    }

    /**
     * A conjunction, a disjunction and a statement read where an operation answers are made only
     * by joining what they hold, which is what lets a reader that changes none of their parts hand
     * one back as it is ({@link WhereEachLineDecides#with}): made anywhere else, one could hold
     * its parts unjoined, and making it again would give another.
     */
    @Test
    void whatJoinsPartsIsMadeOnlyByItsJoining() {
        for (Class<?> joined : List.of(Proposition.All.class, Proposition.Any.class,
                Proposition.WhereItAnswers.class)) {
            Set<String> elsewhere = new TreeSet<>(WhatWasCompiled.callersOf(joined, "<init>"));
            assertTrue(elsewhere.remove(Proposition.class.getName()),
                    "the joining makes " + joined.getSimpleName()
                            + ", and the census sees nobody making one");
            // Its own constructors, one handing the other what the record holds, and no other
            // method of it: the census above is of classes, so that much is asked of its code.
            elsewhere.remove(joined.getName());
            assertEquals(Set.of(), elsewhere,
                    joined.getSimpleName() + " made elsewhere than by its joining");
            assertEquals(Set.of(), methodsMaking(joined),
                    joined.getSimpleName() + " made by a method of its own");
        }
    }

    /** The methods of {@code made} other than its constructors whose code makes one of it. */
    private static Set<String> methodsMaking(Class<?> made) {
        ClassModel model = WhatWasCompiled.compiled().find(made.getName()).orElseThrow();
        String self = model.thisClass().asInternalName();
        Set<String> out = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            if ("<init>".equals(method.methodName().stringValue())) {
                continue;
            }
            method.code().ifPresent(code -> code.forEach(element -> {
                if ((element instanceof NewObjectInstruction created
                        && created.className().asInternalName().equals(self))
                        || (element instanceof InvokeInstruction invoked
                        && invoked.name().stringValue().equals("<init>")
                        && invoked.owner().asInternalName().equals(self))) {
                    out.add(method.methodName().stringValue());
                }
            }));
        }
        return out;
    }

    /** And the rules do build them, so the census above counted something. */
    @Test
    void theRulesBuildThem() {
        assertTrue(WhatWasCompiled.callersOf(Proposition.class, "any")
                        .contains(Derivation.IfThenElse.class.getName()),
                "an if concludes a disjunction, and the census above sees nobody making one");
        assertTrue(WhatWasCompiled.callersOf(Proposition.class, "<init>")
                        .contains(Derivation.ATruthOfASubject.class.getName()),
                "a truth of a subject is built by its rule, and the census above sees nobody"
                        + " building one");
    }
}
