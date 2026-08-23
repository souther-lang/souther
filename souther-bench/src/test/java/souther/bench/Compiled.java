package souther.bench;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.DirectMethodHandleDesc;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What the compiled classes do, read once and in one vocabulary.
 *
 * <p>Read off the bytecode rather than the sources, because that is what the question is. Whether a
 * constructor was invoked is not something a search of text can answer: an
 * {@code import ...Derivation.Complete} and a bare {@code new Complete(...)}, a line break after
 * {@code new}, a static import, a qualified call — all ordinary Java, and all read past a pattern
 * written for one spelling.
 *
 * <p><b>Three ways, and a check that leaves one out is a check with a way round it.</b> A reference
 * is the call it stands for and puts neither an invoke nor a {@code new} in the caller's code: it
 * arrives as a method handle in the bootstrap arguments of an {@code invokedynamic}. A check that
 * counted only {@code new} would be passed by {@code Complete::new} — which is why this is one
 * place and not a vocabulary each check writes out again. The first check here worked it out; the
 * second copied the module walk and not this, and was evadable by exactly the reference the first
 * one names.
 */
final class Compiled {

    private Compiled() {}

    /** How a class reaches something: it makes one, it calls one, it names one for later, or it
     *  reads one. */
    enum How {

        /** A {@code new}. */
        MAKES,

        /** An invocation of any kind. */
        CALLS,

        /** A method or constructor named as a reference, which runs somewhere else. */
        REFERS,

        /**
         * A field read or written, which is how a class reaches a constant.
         *
         * <p>Here because a rule about who may read an {@code enum} had nothing to look at without
         * it: {@code status == Some.CONSTANT} is a {@code getstatic} and none of the three above, so
         * a check written over calls alone met no reader at all and passed by seeing nothing. What a
         * class does is this type's to know, and a rule that needs a way of reaching something asks
         * for it here rather than being written over the nearest vocabulary to hand.
         */
        READS,

        /**
         * A type asked of a value with {@code instanceof}, which is how a class decides for itself
         * what something is.
         *
         * <p>Here because a rule that a sum is read by switching over it had nothing to look at
         * otherwise. An exhaustive {@code switch} over a sealed type is one {@code invokedynamic}
         * and stops when the sum grows; the same reader written as an {@code instanceof} compiles
         * unchanged and answers about the arms it knew — silently, and in whichever direction the
         * author's {@code else} went. The two are the same question in the source and different
         * instructions here, which is what makes the difference checkable at all.
         *
         * <p>{@code instanceof} and not a cast. A cast is something javac writes for itself wherever
         * a generic is read, so a rule counting those would be about the compiler's output rather
         * than about anything anybody wrote.
         */
        ASKS
    }

    /**
     * One thing one method of one class does.
     *
     * @param from       the class whose code holds it, nested names and all. What a rule is about
     *                   is the reader's to decide — one wants the class as it is written and one
     *                   wants the nest — so nothing is folded away here
     * @param method     the method whose code holds it, {@code <clinit>} for a static initialiser
     * @param descriptor that method's parameters and result, so that two overloads are two methods
     * @param owner      what is reached
     * @param member     which member of it, {@code <init>} for a construction
     */
    record Site(String from, String method, String descriptor, How how, String owner, String member,
                boolean isStatic) {

        /** Whether this makes a value of {@code type}, however the source spelled it. */
        boolean makesA(String type) {
            return owner.equals(type) && (how == How.MAKES
                    || (how == How.REFERS && member.equals("<init>")));
        }

        /** The method it is in, which is what a rule naming one method is about. */
        String at() {
            return from + "#" + method + descriptor;
        }
    }

    /** Everything every compiled class of every module does. */
    static List<Site> sites() throws IOException {
        List<Site> found = new ArrayList<>();
        for (Path each : Reactor.classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String from = named(model.thisClass().asInternalName());
            for (var method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                String name = method.methodName().stringValue();
                String descriptor = method.methodType().stringValue();
                for (var element : code) {
                    switch (element) {
                        case InvokeInstruction call -> found.add(new Site(from, name, descriptor,
                                How.CALLS, named(call.owner().asInternalName()),
                                call.name().stringValue(), call.opcode() == Opcode.INVOKESTATIC));
                        case NewObjectInstruction made -> found.add(new Site(from, name, descriptor,
                                How.MAKES, named(made.className().asInternalName()), "<init>",
                                false));
                        case TypeCheckInstruction asked
                                when asked.opcode() == Opcode.INSTANCEOF ->
                                found.add(new Site(from, name, descriptor, How.ASKS,
                                        named(asked.type().asInternalName()), "instanceof", false));
                        case FieldInstruction field -> found.add(new Site(from, name, descriptor,
                                How.READS, named(field.owner().asInternalName()),
                                field.name().stringValue(),
                                field.opcode() == Opcode.GETSTATIC
                                        || field.opcode() == Opcode.PUTSTATIC));
                        case InvokeDynamicInstruction reference -> {
                            for (var argument : reference.bootstrapArgs()) {
                                if (argument instanceof DirectMethodHandleDesc handle) {
                                    found.add(referred(from, name, descriptor, handle));
                                }
                            }
                        }
                        default -> { }
                    }
                }
            }
        }
        assertFalse(found.isEmpty(), "no compiled call was read at all");
        return found;
    }

    private static Site referred(String from, String method, String descriptor,
                                 DirectMethodHandleDesc handle) {
        String owner = handle.owner().descriptorString();
        owner = owner.startsWith("L") && owner.endsWith(";")
                ? owner.substring(1, owner.length() - 1).replace('/', '.') : owner;
        return switch (handle.kind()) {
            case STATIC, INTERFACE_STATIC ->
                    new Site(from, method, descriptor, How.REFERS, owner, handle.methodName(), true);
            case CONSTRUCTOR ->
                    new Site(from, method, descriptor, How.REFERS, owner, "<init>", false);
            default ->
                    new Site(from, method, descriptor, How.REFERS, owner, handle.methodName(), false);
        };
    }

    private static String named(String internal) {
        return internal.replace('/', '.');
    }
}
