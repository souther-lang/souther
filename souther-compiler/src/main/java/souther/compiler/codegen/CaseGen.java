package souther.compiler.codegen;

import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.util.List;

import static souther.compiler.codegen.Descriptors.CD_OptionNone;
import static souther.compiler.codegen.Descriptors.CD_OptionSome;
import static souther.compiler.codegen.Descriptors.MTD_Object;

/**
 * Testing whether a value is a case, and reading the value out of the carrier once it is.
 *
 * <p>These two are what every reader of a {@link CaseSelector} needs and all that they share. How
 * several of them are put together is not here and is not the same question: a {@code match} takes
 * the first arm whose selector answers, and a behavior's declared relation holds every rule whose
 * selector answers. Sharing the composition as well is what made one emitter's rule the other's, so
 * only the test and the projection are shared and each caller writes its own control flow.
 *
 * <p>Nothing here decides what a case means. Which carrier a selector has was settled where the
 * subject's cases were worked out, and this reads the answer.
 */
final class CaseGen {

    private CaseGen() {}

    /** The class a selector's carrier is: the case's own class, or one of the two an optional is
     *  represented by. */
    static ClassDesc carrierOf(CodegenContext ctx, CaseSelector selector) {
        return switch (selector.refinement()) {
            case Refinement.Direct ignored -> ctx.matchCaseClass(selector.name());
            case Refinement.OptionPresent ignored -> CD_OptionSome;
            case Refinement.OptionAbsent ignored -> CD_OptionNone;
        };
    }

    /** Tests the value in {@code subjectSlot} and jumps to {@code noMatch} when it is not this case. */
    static void jumpUnlessMatches(CodeBuilder code, CodegenContext ctx, CaseSelector selector,
                                  int subjectSlot, Label noMatch) {
        code.aload(subjectSlot);
        code.instanceOf(carrierOf(ctx, selector));
        code.ifeq(noMatch);
    }

    /**
     * The same for several selectors at once: falls through when the value is any of them and jumps
     * to {@code noMatch} when it is none.
     *
     * <p>Written as its own emission rather than as a loop over the single-selector one, because the
     * jumps run the other way — each test that answers goes to the code below, and only running out
     * of them is the miss.
     */
    static void jumpUnlessAny(CodeBuilder code, CodegenContext ctx, List<CaseSelector> selectors,
                              int subjectSlot, Label noMatch) {
        if (selectors.size() == 1) {
            jumpUnlessMatches(code, ctx, selectors.get(0), subjectSlot, noMatch);
            return;
        }
        Label matched = code.newLabel();
        for (CaseSelector selector : selectors) {
            code.aload(subjectSlot);
            code.instanceOf(carrierOf(ctx, selector));
            code.ifne(matched);
        }
        code.goto_(noMatch);
        code.labelBinding(matched);
    }

    /**
     * Pushes what {@code refinement} refines the value in {@code subjectSlot} to, boxed as the
     * carrier holds it. The caller converts and stores it — where a bound value lives is the
     * caller's, and only how it is reached is here.
     *
     * <p>Nothing is pushed for a carrier with nothing under it.
     */
    static void pushBound(CodeBuilder code, Refinement refinement, int subjectSlot) {
        switch (refinement) {
            case Refinement.OptionPresent ignored -> {
                code.aload(subjectSlot);
                code.checkcast(CD_OptionSome);
                code.invokevirtual(CD_OptionSome, "value", MTD_Object);
            }
            case Refinement.Direct ignored -> code.aload(subjectSlot);
            case Refinement.OptionAbsent ignored -> { }
        }
    }
}
