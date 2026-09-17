package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LoadInstruction;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value that holds a question about the declarations refuses to be built without it.
 *
 * <p>The questions a reader asks of a declaration it did not write are separate on purpose: which
 * form it is, what it wraps, what its fields hold, what it says. A reader asks the ones it uses, so
 * which of them a value holds differs from value to value and there is no one carrier to put them
 * in — and a value that holds one has been handed it by whoever built it, which is where handing it
 * nothing goes wrong.
 *
 * <p><b>Why this is a rule.</b> A carrier says which questions it holds in its component list and
 * refuses the ones it holds in a condition written out by hand. The two say the same thing until a
 * question is added to one of them: {@code CheckContext} took what each field holds as a peer of
 * what a name wraps, said so where it is declared, and went on accepting nothing for it. Every
 * production caller filled it in, so nothing failed.
 *
 * <p><b>Why it reads the classes and not the source.</b> A rule over the text is a rule about a
 * spelling, and the language admits more spellings than one can be written against: a component
 * whose type is written out with its package, a record that takes a type parameter, a refusal
 * spelled {@code requireNonNull}, a condition written after a block. Each of those left a carrier
 * outside the population of the source rule this replaces, and the first two were already written
 * here. A record's components and what its constructor branches on are the language's own answers,
 * so this asks for those instead.
 */
class ACarrierOfADeclarationQuestionRefusesToBeBuiltWithoutItTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * The questions, by the type a component of one holds.
     *
     * <p>Named here rather than found by what implements something. They are separate interfaces
     * because they are separate questions, so there is nothing they share for this to look for —
     * and a marker they all carried would be a category invented to let this be written.
     */
    private static final Set<String> QUESTIONS = Set.of(
            "Lsouther/compiler/check/PublishedDeclarations;",
            "Lsouther/compiler/check/DeclarationKinds;",
            "Lsouther/compiler/check/NewtypeInners;",
            "Lsouther/compiler/check/EffectiveFieldTypes;",
            "Lsouther/compiler/check/DeclarationNewtypes;",
            "Lsouther/compiler/check/FieldBindings;",
            "Lsouther/compiler/check/ClauseLocations;",
            "Lsouther/compiler/check/ExpandedClauseLookup;",
            "Lsouther/compiler/check/DeclarationLocations;");

    /**
     * The one carrier this does not ask it of, by the whole of what it is.
     *
     * <p>{@code CheckContext.Same} is a context being written out of another one: it is built from
     * the components of a {@code CheckContext} that has already refused them, and there is no path
     * that hands it anything else. A condition of its own would never be reached, and a law about
     * an unreachable state reads as a case somebody had thought about.
     *
     * <p>Said by its owner and not by its name. There is a second {@code Same} in this repository
     * and there will be others; an exception written as a name is an exception to whichever of them
     * comes to hold one of these questions.
     */
    private static final String BUILT_FROM_A_CARRIER_THAT_REFUSED_THEM =
            "souther/compiler/check/CheckContext$Same";

    @Test
    void everyCarrierThatHoldsOneRefusesToBeBuiltWithoutIt() {
        List<String> accepted = new ArrayList<>();
        List<String> carriers = new ArrayList<>();
        for (ClassModel model : COMPILED.all()) {
            List<RecordComponentInfo> components = model.findAttribute(Attributes.record())
                    .map(RecordAttribute::components).orElse(List.of());
            List<String> held = new ArrayList<>();
            for (RecordComponentInfo component : components) {
                if (QUESTIONS.contains(component.descriptor().stringValue())) {
                    held.add(component.name().stringValue());
                }
            }
            String carrier = model.thisClass().asInternalName();
            if (held.isEmpty() || carrier.equals(BUILT_FROM_A_CARRIER_THAT_REFUSED_THEM)) {
                continue;
            }
            carriers.add(carrier);
            Set<String> refused = refusedBy(canonical(model, components), components);
            for (String question : held) {
                if (!refused.contains(question)) {
                    accepted.add(carrier + " holds " + question + " and is built without it");
                }
            }
        }

        assertTrue(carriers.size() > 5,
                () -> "only these carriers were found, so this scanned nothing: " + carriers);
        assertEquals(List.of(), accepted,
                "a carrier that holds a question about the declarations and accepts nothing for it"
                        + " — the component was added to what it holds and not to what it refuses");
    }

    /**
     * The constructor that takes the components, which is the one every other way in goes through.
     *
     * <p>Found by what it takes rather than by being the only one: a carrier may be built by a
     * constructor that fills a component in, and what such a one delegates to is this.
     */
    private static MethodModel canonical(ClassModel model, List<RecordComponentInfo> components) {
        String takes = "(" + components.stream()
                .map(component -> component.descriptor().stringValue())
                .reduce("", String::concat) + ")V";
        for (MethodModel method : model.methods()) {
            if (method.methodName().equalsString("<init>")
                    && method.methodType().equalsString(takes)) {
                return method;
            }
        }
        throw new AssertionError(model.thisClass().asInternalName()
                + " is a record with no constructor over its components, which javac does not make");
    }

    /**
     * Which components {@code made} reads and asks whether they are there.
     *
     * <p>A branch on the parameter or a hand to {@code requireNonNull}: the two spellings a refusal
     * has, both of which come out as the parameter being loaded and something being decided about
     * it. What is done about the answer is the carrier's — a throw, a message — and is not what this
     * is about.
     *
     * <p>Every carrier here is written the first way, so the second is read by nothing in this
     * repository. It is here because the spelling is one this repository uses elsewhere, and it was
     * established by writing one carrier the second way and seeing this go on holding — which also
     * found that a refusal given a message loads it between the two, and that clearing what was
     * read on anything at all left that spelling unread.
     */
    private static Set<String> refusedBy(MethodModel made, List<RecordComponentInfo> components) {
        Set<String> refused = new LinkedHashSet<>();
        made.code().ifPresent(code -> {
            // The parameter last read, which is what a decision about one is made of. Kept across
            // whatever is written between the two — the message a refusal is given is loaded there,
            // and clearing this on anything at all is how the second spelling went unread.
            int[] read = {-1};
            for (CodeElement element : code) {
                switch (element) {
                    case LoadInstruction load -> read[0] = load.slot();
                    case BranchInstruction branch -> {
                        if (branch.opcode() == Opcode.IFNULL
                                || branch.opcode() == Opcode.IFNONNULL) {
                            componentAt(read[0], components).ifPresent(refused::add);
                        }
                        read[0] = -1;
                    }
                    case InvokeInstruction invoked -> {
                        if (invoked.owner().asInternalName().equals("java/util/Objects")
                                && invoked.name().equalsString("requireNonNull")) {
                            componentAt(read[0], components).ifPresent(refused::add);
                        }
                        read[0] = -1;
                    }
                    default -> { }
                }
            }
        });
        return refused;
    }

    /**
     * Which component the local at {@code slot} is, where it is one.
     *
     * <p>Counted the way the frame is laid out — {@code this}, then the components in order, with
     * the wide ones taking two — because that is what a parameter is before it has a name to be
     * read by.
     */
    private static java.util.Optional<String> componentAt(int slot,
                                                          List<RecordComponentInfo> components) {
        int at = 1;
        for (RecordComponentInfo component : components) {
            if (at == slot) {
                return java.util.Optional.of(component.name().stringValue());
            }
            String descriptor = component.descriptor().stringValue();
            at += descriptor.equals("J") || descriptor.equals("D") ? 2 : 1;
        }
        return java.util.Optional.empty();
    }

    /**
     * A record that takes a type parameter is in the population, which the source rule this
     * replaces could not see.
     *
     * <p>Held of this repository rather than of a fixture, because what it is about is the scan: a
     * population defined by a shape the language admits more of is a population with a way out of
     * it, and the way out was already written here.
     */
    @Test
    void aCarrierThatTakesATypeParameterIsReadLikeAnyOther() {
        List<String> generic = new ArrayList<>();
        for (ClassModel model : COMPILED.all()) {
            boolean takesOne = model.findAttribute(Attributes.signature())
                    .map(signature -> signature.signature().stringValue().startsWith("<"))
                    .orElse(false);
            if (takesOne && model.findAttribute(Attributes.record()).isPresent()) {
                generic.add(model.thisClass().asInternalName());
            }
        }
        assertFalse(generic.isEmpty(),
                "this repository writes no record over a type parameter, so nothing says the scan"
                        + " reads one");
    }
}
