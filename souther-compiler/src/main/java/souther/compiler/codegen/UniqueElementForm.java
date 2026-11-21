package souther.compiler.codegen;

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
import static souther.compiler.codegen.Descriptors.MTD_ArrayList_add;
import static souther.compiler.codegen.Descriptors.MTD_List_copyOf;
import static souther.compiler.codegen.Descriptors.MTD_hasNext;
import static souther.compiler.codegen.Descriptors.MTD_iterator;
import static souther.compiler.codegen.Descriptors.MTD_next;
import static souther.compiler.codegen.Descriptors.MTD_void;

/**
 * The form a repeated element of a {@link BoundaryConstraint.Unique} list is reported in: the form
 * the checker stated the constraint with ({@link BoundaryConstraint.Unique#element()}), a newtype as
 * the value it wraps, at whatever depth of list it stands. Only what the refusal holds is unwrapped;
 * which elements repeat is found by {@code Decoding.unique} over the elements themselves, by the
 * language's equality ({@code Sets.repeated}).
 *
 * <p>Emitted as a static method of the decoder class, {@code __uniqueForm(Object):Object}, and
 * handed to {@code Decoding.unique} as a {@code Function}. A list that stands in an element and
 * holds something to unwrap is written by a helper of its own, named for how many lists stand above
 * it.
 */
final class UniqueElementForm {

    private static final String FORM = "__uniqueForm";

    /** The helpers that write a list standing in an element, each named for how many lists stand
     *  above it. */
    private static final String WRITTEN = "__uniqueWritten$";

    /** {@code static Object __uniqueForm(Object)} and its list helpers. */
    private static final MethodTypeDesc MTD_written = MethodTypeDesc.of(ConstantDescs.CD_Object,
            ConstantDescs.CD_Object);

    private UniqueElementForm() {}

    /** Pushes the {@code Function} that writes one element in its reported form. */
    static void push(CodeBuilder code, ClassDesc decoderClass) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, decoderClass, FORM, MTD_written);
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_written));
    }

    /**
     * Emits {@code __uniqueForm} onto the decoder class being built, and the helpers it writes a
     * list standing in an element with.
     *
     * @param element the form the elements are reported in
     */
    static void emitHelpers(CodegenContext ctx, ClassBuilder cb, ClassDesc decoderClass,
                            MessageForm element) {
        cb.withMethodBody(FORM, MTD_written, ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                code -> {
            code.aload(0);
            emitWritten(ctx, code, decoderClass, element, 0);
            code.areturn();
        });
        int lists = 0;
        MessageForm at = element;
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
     * Leaves on the stack, in place of the value on top of it, what the refusal holds for that value
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
     * {@code static Object __uniqueWritten$n(Object xs)}: the list of what each element of
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
}
