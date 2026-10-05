package souther.compiler.codegen;

import net.unit8.raoh.ErrorCodes;
import souther.compiler.check.NewtypeInners;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.MessageForm;
import souther.compiler.types.Type;

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
import static souther.compiler.codegen.Descriptors.MTD_Sets_repeated;
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
 * ({@code flatMapWithPath}), finding the repeats by the same equality the language's own
 * {@code List.distinct} reads (souther/list.sou, {@code Sets.repeated}), and failing
 * with the issue Raoh's constraint fails with when it finds one: {@code duplicate_element} with
 * {@code duplicates} holding each repeated element once, in the order its repetition was found, and
 * Raoh's default message.
 *
 * <p>Each element is put in {@code duplicates} in the form the checker stated the constraint with
 * ({@link BoundaryConstraint.Unique#element()}): a newtype as the value it wraps, at whatever depth
 * of list it stands. Only what the issue holds is unwrapped; the walk compares the elements
 * themselves.
 *
 * <p>Raoh's {@code contains}, {@code containsAll} and {@code toSet} share {@code unique()}'s own
 * defect — a {@code HashSet}-backed membership, so JVM equality rather than Souther's — and
 * {@code BoundaryConstraint.OfList} has no clause lowered to them today. Were one added, it would
 * need the same walk this class uses, not a call into one of them.
 *
 * <p>That issue is written out here, and so it is a copy of Raoh's. Which constraint a clause is was
 * decided by the checker; this only says what Raoh calls it, and a Raoh that came to call it
 * something else is caught by the test that holds the two issues equal.
 */
final class RaohListUnique {

    private static final String HELPER = "__listUnique";

    /** The helpers that write a list standing in an element, each named for how many lists stand
     *  above it. */
    private static final String WRITTEN = "__listUniqueWritten$";

    /** {@code Result.failWith(Path, String code, String message, String defaultMessage, Map meta)}. */
    private static final MethodTypeDesc MTD_failWith = MethodTypeDesc.of(CD_RResult, CD_RPath,
            CD_String, CD_String, CD_String, CD_Map);

    /** {@code static Object __listUniqueWritten$n(Object)}. */
    private static final MethodTypeDesc MTD_written = MethodTypeDesc.of(ConstantDescs.CD_Object,
            ConstantDescs.CD_Object);

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

    /**
     * Emits the helper {@link #emit} chains onto the decoder class being built, and the helpers it
     * writes a repeated element with where that element is written as something other than itself.
     *
     * @param element the form the elements are reported in
     */
    static void emitHelpers(CodegenContext ctx, ClassBuilder cb, ClassDesc decoderClass,
                            MessageForm element) {
        cb.withMethodBody(HELPER, MTD_invariantFailure,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                code -> emitBody(ctx, code, decoderClass, element));
        // The duplicates themselves are the outermost list written.
        int lists = 0;
        MessageForm at = new MessageForm.ListOf(element);
        while (!(at instanceof MessageForm.Scalar)) {
            if (at instanceof MessageForm.Newtype newtype) {
                at = newtype.wraps();
            } else if (at instanceof MessageForm.ListOf list) {
                if (list.unwraps()) {
                    int above = lists + 1;
                    cb.withMethodBody(WRITTEN + lists, MTD_written,
                            ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                            code -> emitWrittenList(ctx, code, decoderClass, list, above));
                }
                lists++;
                at = list.element();
            }
        }
    }

    /**
     * Leaves on the stack, in place of the value on top of it, what the issue holds for that value
     * written in {@code form}.
     *
     * @param lists how many lists stand above the value, which names the helper a list in it is
     *     written by
     */
    private static void emitWritten(CodegenContext ctx, CodeBuilder code, ClassDesc decoderClass,
                                    MessageForm form, int lists) {
        switch (form) {
            case MessageForm.Scalar _ -> { }
            case MessageForm.Newtype newtype -> {
                Type wraps = newtype.wraps().type();
                ClassDesc named = ctx.cd(newtype.name());
                code.checkcast(named);
                code.invokevirtual(named, NewtypeInners.THE_ONE_VALUE,
                        MethodTypeDesc.of(JvmTypes.jvmType(wraps, ctx)));
                JvmTypes.box(code, wraps);
                emitWritten(ctx, code, decoderClass, newtype.wraps(), lists);
            }
            case MessageForm.ListOf list -> {
                if (list.unwraps()) {
                    code.invokestatic(decoderClass, WRITTEN + lists, MTD_written);
                }
            }
        }
    }

    /**
     * {@code static Object __listUniqueWritten$n(Object xs)}: the list of what each element of
     * {@code xs} is written as.
     *
     * <p>Locals: {@code xs}=0, {@code it}=1, {@code out}=2.
     */
    private static void emitWrittenList(CodegenContext ctx, CodeBuilder code,
                                        ClassDesc decoderClass, MessageForm.ListOf list,
                                        int lists) {
        code.new_(CD_ArrayList);
        code.dup();
        code.invokespecial(CD_ArrayList, "<init>", MTD_void);
        code.astore(2);                                              // out = new ArrayList()
        code.aload(0);
        code.checkcast(CD_List);
        code.invokeinterface(CD_List, "iterator", MTD_iterator);
        code.astore(1);                                              // it = ((List) xs).iterator()

        Label loop = code.newLabel();
        Label done = code.newLabel();
        code.labelBinding(loop);
        code.aload(1);
        code.invokeinterface(CD_Iterator, "hasNext", MTD_hasNext);
        code.ifeq(done);
        code.aload(2);
        code.aload(1);
        code.invokeinterface(CD_Iterator, "next", MTD_next);
        emitWritten(ctx, code, decoderClass, list.element(), lists);
        code.invokevirtual(CD_ArrayList, "add", MTD_ArrayList_add);
        code.pop();                                                  // out.add(written(it.next()))
        ctx.countOneStep(code);
        code.goto_(loop);

        code.labelBinding(done);
        code.aload(2);
        code.invokestatic(CD_List, "copyOf", MTD_List_copyOf, true);
        code.areturn();
    }

    /**
     * {@code static Result __listUnique(Object value, Path path)}: {@code value}, where nothing in
     * it repeats, and otherwise what Raoh's {@code unique} fails with — {@code duplicate_element}
     * with the repeats found.
     *
     * <p>Locals: {@code value}=0, {@code path}=1, {@code duplicates}=2.
     */
    private static void emitBody(CodegenContext ctx, CodeBuilder code, ClassDesc decoderClass,
                                 MessageForm element) {
        code.aload(0);
        code.checkcast(CD_List);
        ctx.callRuntime(code, CD_Sets, "repeated", MTD_Sets_repeated, Work.CHECKPOINTED);
        code.astore(2);                                     // duplicates = Sets.repeated((List) value)
        code.aload(2);
        code.invokeinterface(CD_List, "isEmpty", MethodTypeDesc.of(ConstantDescs.CD_boolean));
        Label fail = code.newLabel();
        code.ifeq(fail);
        code.aload(0);
        code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
        code.areturn();

        code.labelBinding(fail);
        code.aload(2);
        emitWritten(ctx, code, decoderClass, new MessageForm.ListOf(element), 0);
        code.astore(2);                                     // duplicates, as the issue writes them
        code.aload(1);                                               // path
        code.loadConstant(ErrorCodes.DUPLICATE_ELEMENT);
        code.aconst_null();                                          // no custom message
        code.new_(CD_StringBuilder);
        code.dup();
        code.invokespecial(CD_StringBuilder, "<init>", MTD_void);
        code.loadConstant("must not contain duplicates: ");
        code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendString);
        code.aload(2);
        code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendObject);
        code.invokevirtual(CD_StringBuilder, "toString", MTD_toString);
        code.loadConstant("duplicates");
        code.aload(2);
        code.invokestatic(CD_Map, "of", MTD_mapOfOne, true);
        code.invokestatic(CD_RResult, "failWith", MTD_failWith, true);
        code.areturn();
    }
}
