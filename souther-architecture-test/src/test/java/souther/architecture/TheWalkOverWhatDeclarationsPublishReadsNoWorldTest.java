package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the walk over which rules govern a value reads, written down.
 *
 * <p>One authority. What a declaration spreads, what it states, and whether there is a declaration
 * at all are read from what the declarations publish; a second place answering any of it is a walk
 * whose answer depends on which of the two it met.
 *
 * <p><b>Written as what it may read and not as what it may not.</b> A rule naming the worlds would
 * be answered by asking a narrower carrier for the same thing — the scope this used to consult
 * reaches its answer through {@code NameSense}, which any carrier of it can hand over, and a rule
 * listing the worlds would let that back in with nothing going red. So every type of this compiler
 * the walk names is a row here, and a second authority arriving is a row nobody wrote.
 *
 * <p>Read off the compiled class: the constant pool for what it uses, and the descriptors and
 * signatures of its methods and fields for what it is handed and hands on. A type reached by being
 * passed in, held, or answered with is named in one of those, so a carrier with a world inside it is
 * a row too.
 */
class TheWalkOverWhatDeclarationsPublishReadsNoWorldTest {

    private static final String THE_WALK = "souther/compiler/check/PublishedRules";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * Every type of this compiler the walk names, and why it may.
     *
     * <p>{@code PublishedDeclarations} is the authority, and {@code PublishedDeclarationResult} is
     * what it answers — which of the three, and what the declaration says where there is one.
     * {@code DeclarationMeaning} and {@code ClauseMeaning} are that answer read: what a declaration
     * spreads and what each of its clauses states. {@code DeclarationReference} is what a spread
     * names and {@code TypeSymbol} is what it resolves to, which is where the walk goes next;
     * {@code TypeKey} is the address the authority is asked by.
     *
     * <p>Nothing here reads a declaration as it was written, and nothing here answers a question
     * about one from anywhere but the publication.
     */
    private static final List<String> IT_MAY_READ = List.of(
            "souther/compiler/check/ClauseMeaning",
            "souther/compiler/check/DeclarationMeaning",
            "souther/compiler/check/DeclarationMeaning$Product",
            "souther/compiler/check/DeclarationReference",
            "souther/compiler/check/DeclarationReference$Named",
            "souther/compiler/check/PublishedDeclarationResult",
            "souther/compiler/check/PublishedDeclarationResult$Found",
            "souther/compiler/check/PublishedDeclarationResult$NotDeclared",
            "souther/compiler/check/PublishedDeclarationResult$Unavailable",
            "souther/compiler/check/PublishedDeclarations",
            "souther/compiler/check/PublishedRules",
            "souther/compiler/types/TypeKey",
            "souther/compiler/types/TypeSymbol",
            "souther/compiler/types/TypeSymbol$AtModule");

    @Test
    void theWalkNamesWhatIsWrittenDownAndNothingElse() {
        assertEquals(IT_MAY_READ, new ArrayList<>(named()),
                "a row missing here is a second authority the walk reads, which is an answer that"
                        + " depends on which of the two it met");
    }

    /** Every type of this compiler the walk names, used or written in a signature. */
    private static Set<String> named() {
        ClassModel walk = COMPILED.read(THE_WALK);
        Set<String> found = new TreeSet<>();
        for (PoolEntry entry : walk.constantPool()) {
            if (entry instanceof ClassEntry it) {
                add(found, it.asInternalName());
            }
            if (entry instanceof MemberRefEntry it) {
                add(found, it.owner().name().stringValue());
                addEachIn(found, it.nameAndType().type().stringValue());
            }
        }
        for (MethodModel method : walk.methods()) {
            addEachIn(found, method.methodTypeSymbol().descriptorString());
            method.findAttribute(Attributes.signature()).ifPresent(
                    it -> addEachIn(found, it.signature().stringValue()));
        }
        for (FieldModel field : walk.fields()) {
            addEachIn(found, field.fieldTypeSymbol().descriptorString());
            field.findAttribute(Attributes.signature()).ifPresent(
                    it -> addEachIn(found, it.signature().stringValue()));
        }
        return found;
    }

    /** Every class named in a descriptor or a signature, which is where a type handed over or
     *  handed on is written. */
    private static void addEachIn(Set<String> found, String descriptor) {
        Matcher named = Pattern.compile("L([^;<]+)[;<]").matcher(descriptor);
        while (named.find()) {
            add(found, named.group(1));
        }
    }

    /** This compiler's own types only. What the walk does with a list or a map is the language's
     *  and says nothing about which authority it read. */
    private static void add(Set<String> found, String name) {
        if (name.startsWith("souther/")) {
            found.add(name);
        }
    }
}
