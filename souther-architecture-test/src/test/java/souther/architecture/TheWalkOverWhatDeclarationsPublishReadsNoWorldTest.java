package souther.architecture;

import souther.compiler.check.PublishedDeclarations;
import souther.compiler.check.Symbols;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk over which rules govern a value takes what the declarations publish, and nothing beside
 * it.
 *
 * <p>What it would otherwise reach for is a world. Told that a declaration says nothing, a walk has
 * to know which of two opposite things that is — nothing declares the name, or a declaration is
 * there whose module could not be read — and only one of them leaves the rules of a value short.
 * Read out of a world, that bit comes from where the declarations are written, which is the thing a
 * walk over what they publish is for not reading.
 *
 * <p>So what is published says which of the three it is
 * ({@code souther.compiler.check.PublishedDeclarationResult}) and the walk asks nobody else. Held
 * here rather than left to the signature: a world is reached by being named in one, and also by
 * being handed on, held in a record, or read off something that has one — and a parameter removed
 * while a field stays is the same walk reading the same thing.
 *
 * <p>The worlds are read off the sealed interface and not listed, so a world added to it is one
 * this sees arrive.
 *
 * <p>The control is what the walk does take. Without it this is met by a class that reads neither,
 * which is not a walk over what declarations publish at all.
 */
class TheWalkOverWhatDeclarationsPublishReadsNoWorldTest {

    private static final String THE_WALK = "souther/compiler/check/PublishedRules";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** Every declaration world, the interface and each carrier of it. */
    private static final Set<String> THE_WORLDS = worlds();

    @Test
    void theWalkNamesNoWorld() {
        assertEquals(List.of(), new ArrayList<>(named(THE_WORLDS)),
                "the walk over what declarations publish reads a world, so which of the two ways a"
                        + " declaration says nothing is answered from where it is written");
    }

    /** And it names what it does read, which is what keeps the rule above from holding vacuously. */
    @Test
    void andItNamesWhatItReadsInstead() {
        assertTrue(named(Set.of(internal(PublishedDeclarations.class))).size() == 1,
                "the walk does not read what the declarations publish either, so it is not the walk"
                        + " this is about");
    }

    /** Which of {@code wanted} the walk names — used, handed on, or written in a signature. */
    private static Set<String> named(Set<String> wanted) {
        ClassModel walk = COMPILED.read(THE_WALK);
        Set<String> found = new TreeSet<>();
        for (PoolEntry entry : walk.constantPool()) {
            if (entry instanceof ClassEntry it && wanted.contains(it.asInternalName())) {
                found.add(it.asInternalName());
            }
        }
        for (MethodModel method : walk.methods()) {
            for (String each : wanted) {
                if (writes(method, each)) {
                    found.add(each);
                }
            }
        }
        return found;
    }

    /** Whether {@code method} writes {@code type} in what it takes or answers with. */
    private static boolean writes(MethodModel method, String type) {
        String named = "L" + type + ";";
        if (method.methodTypeSymbol().descriptorString().contains(named)) {
            return true;
        }
        return method.findAttribute(Attributes.signature())
                .map(SignatureAttribute::signature)
                .map(it -> it.stringValue().contains(named))
                .orElse(false);
    }

    private static Set<String> worlds() {
        Set<String> out = new LinkedHashSet<>();
        out.add(internal(Symbols.class));
        for (Class<?> each : Symbols.class.getPermittedSubclasses()) {
            out.add(internal(each));
        }
        return out;
    }

    private static String internal(Class<?> type) {
        return type.getName().replace('.', '/');
    }
}
