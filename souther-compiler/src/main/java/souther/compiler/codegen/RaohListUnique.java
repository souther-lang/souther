package souther.compiler.codegen;

import net.unit8.raoh.ErrorCodes;
import souther.compiler.core.BoundaryConstraint;

import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;

import static souther.compiler.codegen.Descriptors.CD_ArrayList;
import static souther.compiler.codegen.Descriptors.CD_Iterator;
import static souther.compiler.codegen.Descriptors.CD_List;
import static souther.compiler.codegen.Descriptors.CD_Map;
import static souther.compiler.codegen.Descriptors.CD_RDecoder;
import static souther.compiler.codegen.Descriptors.CD_RPath;
import static souther.compiler.codegen.Descriptors.CD_RResult;
import static souther.compiler.codegen.Descriptors.CD_Sets;
import static souther.compiler.codegen.Descriptors.CD_String;
import static souther.compiler.codegen.Descriptors.CD_StringBuilder;
import static souther.compiler.codegen.Descriptors.MTD_ArrayList_add;
import static souther.compiler.codegen.Descriptors.MTD_List_copyOf;
import static souther.compiler.codegen.Descriptors.MTD_Rok;
import static souther.compiler.codegen.Descriptors.MTD_SB_appendObject;
import static souther.compiler.codegen.Descriptors.MTD_SB_appendString;
import static souther.compiler.codegen.Descriptors.MTD_Sets_contains;
import static souther.compiler.codegen.Descriptors.MTD_Sets_empty;
import static souther.compiler.codegen.Descriptors.MTD_Sets_insert;
import static souther.compiler.codegen.Descriptors.MTD_flatMapWithPath;
import static souther.compiler.codegen.Descriptors.MTD_hasNext;
import static souther.compiler.codegen.Descriptors.MTD_invariantFailure;
import static souther.compiler.codegen.Descriptors.MTD_iterator;
import static souther.compiler.codegen.Descriptors.MTD_mapOfOne;
import static souther.compiler.codegen.Descriptors.MTD_next;
import static souther.compiler.codegen.Descriptors.MTD_toString;
import static souther.compiler.codegen.Descriptors.MTD_void;

/**
 * {@link BoundaryConstraint.Unique}, as the issue Raoh's {@code ListDecoder.unique()} reports for
 * it — but read by the elements' value equality (spec §collections, {@code Values}), not by their
 * JVM representation's {@code equals}. Raoh's own {@code unique()} collects the elements in a
 * {@code HashSet}, so a {@code Decimal} at another scale, or a container holding one, is not the
 * duplicate the clause means. What runs here instead is the generic step every decoder has
 * ({@code flatMapWithPath}), walking the elements with the same membership {@code Set.contains} /
 * {@code Set.insert} the language's own {@code List.distinct} does (souther/list.sou), and failing
 * with the issue Raoh's constraint fails with when it finds one: {@code duplicate_element} with
 * {@code duplicates} holding each repeated element once, in the order its repetition was found, and
 * Raoh's default message.
 *
 * <p>That issue is written out here, and so it is a copy of Raoh's. Which constraint a clause is was
 * decided by the checker; this only says what Raoh calls it, and a Raoh that came to call it
 * something else is caught by the test that holds the two issues equal.
 */
final class RaohListUnique {

    private static final String HELPER = "__listUnique";

    /** {@code Result.failWith(Path, String code, String message, String defaultMessage, Map meta)}. */
    private static final MethodTypeDesc MTD_failWith = MethodTypeDesc.of(CD_RResult, CD_RPath,
            CD_String, CD_String, CD_String, CD_Map);

    private RaohListUnique() {}

    /**
     * Chains the check onto the decoder on the stack, which answers the list the model declares,
     * leaving the decoder that fails where an element repeats.
     */
    static void emit(CodeBuilder code, ClassDesc decoderClass) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, decoderClass, HELPER, MTD_invariantFailure);
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_invariantFailure));
        code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
    }

    /** Emits the helper {@link #emit} chains, onto the decoder class being built. */
    static void emitHelpers(ClassBuilder cb) {
        cb.withMethodBody(HELPER, MTD_invariantFailure,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, RaohListUnique::emitBody);
    }

    /**
     * {@code static Result __listUnique(Object value, Path path)}: {@code value}, where nothing in
     * it repeats, and otherwise what Raoh's {@code unique} fails with — {@code duplicate_element}
     * with the repeats found.
     *
     * <p>Locals: {@code value}=0, {@code path}=1, {@code xs}=2, {@code seen}=3, {@code reported}=4,
     * {@code duplicates}=5, {@code it}=6, {@code x}=7.
     */
    private static void emitBody(CodeBuilder code) {
        code.aload(0);
        code.checkcast(CD_List);
        code.astore(2);                                             // xs = (List) value

        code.invokestatic(CD_Sets, "empty", MTD_Sets_empty);
        code.astore(3);                                              // seen = Sets.empty()
        code.invokestatic(CD_Sets, "empty", MTD_Sets_empty);
        code.astore(4);                                              // reported = Sets.empty()
        code.new_(CD_ArrayList);
        code.dup();
        code.invokespecial(CD_ArrayList, "<init>", MTD_void);
        code.astore(5);                                              // duplicates = new ArrayList()

        code.aload(2);
        code.invokeinterface(CD_List, "iterator", MTD_iterator);
        code.astore(6);                                              // it = xs.iterator()

        Label loop = code.newLabel();
        Label seenBefore = code.newLabel();
        Label done = code.newLabel();
        code.labelBinding(loop);
        code.aload(6);
        code.invokeinterface(CD_Iterator, "hasNext", MTD_hasNext);
        code.ifeq(done);
        code.aload(6);
        code.invokeinterface(CD_Iterator, "next", MTD_next);
        code.astore(7);                                              // x = it.next()

        code.aload(7);
        code.aload(3);
        code.invokestatic(CD_Sets, "contains", MTD_Sets_contains);
        code.ifne(seenBefore);
        // not seen before: seen = Sets.insert(x, seen)
        code.aload(7);
        code.aload(3);
        code.invokestatic(CD_Sets, "insert", MTD_Sets_insert);
        code.astore(3);
        code.goto_(loop);
        code.labelBinding(seenBefore);
        // seen already: a duplicate, reported once — the first time it repeats
        code.aload(7);
        code.aload(4);
        code.invokestatic(CD_Sets, "contains", MTD_Sets_contains);
        code.ifne(loop);
        code.aload(5);
        code.aload(7);
        code.invokevirtual(CD_ArrayList, "add", MTD_ArrayList_add);
        code.pop();
        code.aload(7);
        code.aload(4);
        code.invokestatic(CD_Sets, "insert", MTD_Sets_insert);
        code.astore(4);
        code.goto_(loop);

        code.labelBinding(done);
        code.aload(5);
        code.invokevirtual(CD_ArrayList, "isEmpty", MethodTypeDesc.of(ConstantDescs.CD_boolean));
        Label fail = code.newLabel();
        code.ifeq(fail);
        code.aload(0);
        code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
        code.areturn();

        code.labelBinding(fail);
        code.aload(5);
        code.invokestatic(CD_List, "copyOf", MTD_List_copyOf, true);
        code.astore(5);                                              // duplicates = List.copyOf(...)
        code.aload(1);                                               // path
        code.loadConstant(ErrorCodes.DUPLICATE_ELEMENT);
        code.aconst_null();                                          // no custom message
        code.new_(CD_StringBuilder);
        code.dup();
        code.invokespecial(CD_StringBuilder, "<init>", MTD_void);
        code.loadConstant("must not contain duplicates: ");
        code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendString);
        code.aload(5);
        code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendObject);
        code.invokevirtual(CD_StringBuilder, "toString", MTD_toString);
        code.loadConstant("duplicates");
        code.aload(5);
        code.invokestatic(CD_Map, "of", MTD_mapOfOne, true);
        code.invokestatic(CD_RResult, "failWith", MTD_failWith, true);
        code.areturn();
    }
}
