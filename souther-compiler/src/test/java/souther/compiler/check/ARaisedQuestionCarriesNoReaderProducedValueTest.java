package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.Signatures;
import souther.test.WhatAModuleDeclares;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A question one rule of the model raises carries nothing a reading of that rule produced.
 *
 * <p>What a coverage question is about is the model's: which rule, which place its own rules name,
 * and — for a line — which number of that place, said as the operation the author's call resolved
 * to. All of those a rule has whether or not anything read it. What a reading produces is
 * everything else: the term the number is measured by, the range it runs over, the quantity a
 * clause cuts, the end an invariant placed.
 *
 * <p><b>Why the direction matters.</b> A question holding a reader's value can only be raised where
 * that value could be made, so the reading falling short takes the question away with it — and the
 * model is then short of something with nothing standing for it. That is how a shortfall about a
 * rule came to be carried in a list beside the accounting rather than as an entry in it
 * ({@code BlockReason.RuleWithoutLineReason.leavesShort}). Closing it begins here: a question that
 * can be stated about a rule nobody read is a question that can stand unanswered.
 *
 * <p><b>What this does not say.</b> Not that whether a question is raised is independent of the
 * readings — {@link Required} is still classified from what a reader found the clause to state, and
 * closing that is its own change. This says only that what a question carries is the model's
 * vocabulary, which is what makes the rest of it sayable at all.
 *
 * <p><b>The whole reachable graph and not the roots.</b> A component whose type is model-side and
 * whose own components are not moves the reading one hop away and leaves the claim standing. So the
 * closure is walked — sealed subtypes and record components, through the generic signature so that
 * a type argument is followed rather than erased — and what it comes to is written down here. A
 * type added to it fails this until it is listed, which is where the reason for admitting it gets
 * written.
 *
 * <p><b>And it stops at the three types that are names.</b> A place and an operation are named
 * rather than described: what {@link RuleKey}, {@code TermPath} and {@code ValueName} are made of
 * is how this compiler spells a name, and none of it is an answer about a model. Walked through,
 * this would be reading the whole of the naming machinery and would fail on a change to it that has
 * nothing to say about questions — a check that goes off for unrelated work is one nobody reads.
 * They are reached and not entered, and that they are names is what admits them.
 */
class ARaisedQuestionCarriesNoReaderProducedValueTest {

    /** What a rule raises, and what a question about an input is about: the two ends of the one
     *  crossing, and both are asked here because a crossing can lose a property at either end. */
    private static final List<String> ROOTS = List.of(
            "souther/compiler/check/Owed",
            "souther/compiler/inputs/InputQuestion");

    /** The three types that are how a name is spelled, reached and not entered. */
    private static final Set<String> NAMES = Set.of(
            "souther/compiler/check/RuleKey",
            "souther/compiler/inputs/TermPath",
            "souther/compiler/types/ValueName");

    /**
     * Every type a question is made of.
     *
     * <p>Each of them is something an author wrote or a name this compiler resolved one of their
     * words to, and none of them is an answer about a model. {@link RuleKey} and
     * {@code TermPath} are the two spellings of a place, which is what the crossing translates;
     * {@link BoundaryClaim} is a place and which number of it; {@code ValueName} is the operation
     * that number is taken by, as the call resolved and not as it was written.
     */
    private static final Set<String> THE_QUESTIONS_OWN_VOCABULARY = Set.of(
            "souther/compiler/check/Owed",
            "souther/compiler/check/Owed$AdmittedValues",
            "souther/compiler/check/Owed$Boundary",
            "souther/compiler/check/BoundaryClaim",
            "souther/compiler/check/BoundaryClaim$OfWhatNumber",
            "souther/compiler/check/BoundaryClaim$OfWhatNumber$OfItsOwnValue",
            "souther/compiler/check/BoundaryClaim$OfWhatNumber$OfWhatAnOperationAnswers",
            "souther/compiler/check/RuleKey",
            "souther/compiler/inputs/InputQuestion",
            "souther/compiler/inputs/InputQuestion$AboutAPosition",
            "souther/compiler/inputs/InputQuestion$AboutANumber",
            "souther/compiler/inputs/TermPath",
            "souther/compiler/types/ValueName");

    @Test
    void aQuestionIsMadeOfTheModelsOwnVocabulary() {
        assertEquals(THE_QUESTIONS_OWN_VOCABULARY, reachable(),
                "what a coverage question carries, walked from both ends of the crossing");
    }

    /**
     * And the reading's own values are outside it.
     *
     * <p>Said against names rather than only as the closure above, because the closure is a set
     * this test declares: widened by hand, it admits whatever was added and reports nothing. These
     * are the values a reading makes, and each of them was reachable from a question before.
     */
    @Test
    void noReadingsOwnValueIsInIt() {
        List<String> made = List.of(
                "souther/compiler/inputs/NumericTerm",
                "souther/compiler/check/FieldDomains",
                "souther/compiler/check/InvariantBound",
                "souther/compiler/check/ClauseStates",
                "souther/compiler/numeric/NumericDomain");
        Set<String> reachable = reachable();
        for (String each : made) {
            assertEquals(List.of(), reachable.stream().filter(one -> one.equals(each)
                            || one.startsWith(each + "$")).toList(),
                    each + " is what a reading came to, and a question is asked before there is one");
        }
    }

    /** Every {@code souther} type reachable from the roots, through sealed subtypes and record
     *  components. */
    private static Set<String> reachable() {
        Map<String, ClassModel> byName = new LinkedHashMap<>();
        for (ClassModel each : WhatAModuleDeclares.of(Owed.class).classes()) {
            byName.put(each.thisClass().asInternalName(), each);
        }
        Set<String> seen = new LinkedHashSet<>();
        Deque<String> todo = new ArrayDeque<>(ROOTS);
        while (!todo.isEmpty()) {
            String name = todo.removeFirst();
            if (!name.startsWith("souther/") || !seen.add(name)) {
                continue;
            }
            if (NAMES.contains(name)) {
                continue;
            }
            ClassModel of = byName.get(name);
            if (of == null) {
                // A type of another module of this compiler, which this reading cannot open. It is
                // named in the vocabulary above and answered for there.
                continue;
            }
            of.findAttribute(Attributes.permittedSubclasses())
                    .ifPresent(sealed -> sealed.permittedSubclasses()
                            .forEach(each -> todo.add(each.asInternalName())));
            for (RecordComponentInfo each : of.findAttribute(Attributes.record())
                    .map(RecordAttribute::components).orElse(List.of())) {
                todo.addAll(named(signatureOf(each)));
            }
        }
        return seen;
    }

    /** The component as it was declared, so that a type argument is followed and not erased. */
    private static Signature signatureOf(RecordComponentInfo of) {
        return of.findAttribute(Attributes.signature())
                .map(each -> each.asTypeSignature())
                .orElseGet(() -> Signature.of(of.descriptorSymbol()));
    }

    /** Every class named anywhere in {@code of}, its type arguments included. */
    private static List<String> named(Signature of) {
        List<String> out = new ArrayList<>();
        switch (of) {
            case Signature.ClassTypeSig it -> {
                out.add(Signatures.named(it));
                for (Signature.TypeArg arg : it.typeArgs()) {
                    if (arg instanceof Signature.TypeArg.Bounded bounded) {
                        out.addAll(named(bounded.boundType()));
                    }
                }
            }
            case Signature.ArrayTypeSig it -> out.addAll(named(it.componentSignature()));
            // A type variable is answered where the type is used, which is the signature that
            // named it — so following it here would be following it twice or not at all.
            case Signature.TypeVarSig _, Signature.BaseTypeSig _ -> { }
        }
        return out;
    }
}
