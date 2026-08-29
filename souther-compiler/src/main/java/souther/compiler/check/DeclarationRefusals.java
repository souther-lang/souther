package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.DataMessage;

/**
 * What the author of a module is told about a declaration it may not have.
 *
 * <p>The other side of {@link DeclaredNames}, and deliberately not part of it. Indexing answers
 * which declarations a module has and which rule refused the rest; that answer is the same wherever
 * the module came from. Saying it to somebody is not: this is written for a module of this
 * compilation, whose author holds the file and can be sent to the line. A module read back off an
 * artifact has no such reader, and what a refusal means there is a fact about the artifact
 * ({@link souther.compiler.meta.Readback.Failure}) said to whoever put it on the path.
 *
 * <p>Two doors and one sentence per rule. Which representation the declarations are in decides
 * nothing about what is said — the rule is the same rule on both sides of {@code Resolve} — so the
 * two entries read the name and the place off their own form and meet at one switch.
 */
public final class DeclarationRefusals {

    private DeclarationRefusals() {
    }

    /** How {@code refusal} is said, of a module as it was written. */
    public static Diagnostic reportedAsWritten(DeclaredNames.Refusal<Ast.Def> refusal) {
        Ast.Def def = refusal.refused();
        return said(refusal, def.name(), def.pos(), def.written().reportedAt());
    }

    /** How {@code refusal} is said, of a module something has resolved. */
    public static Diagnostic reportedAsResolved(DeclaredNames.Refusal<Hir.Def> refusal) {
        Hir.Def def = refusal.refused();
        return said(refusal, def.name(), def.pos(), def.written().reportedAt());
    }

    /**
     * The sentence for each rule there is, and a switch with nothing to fall through to: a rule
     * added to the indexing is one this has to have a sentence for.
     */
    private static <D> Diagnostic said(DeclaredNames.Refusal<D> refusal, String name,
                                       SourcePos pos, Region reportedAt) {
        return switch (refusal) {
            case DeclaredNames.Refusal.DeclaredTwice<D> _ -> Diagnostic
                    .at(pos)
                    .say(new DataMessage.ADataIsAlreadyDefined(name)).build();
            case DeclaredNames.Refusal.ABuiltInOptionCaseIsDeclared<D> _ -> Diagnostic
                    .at(reportedAt)
                    .say(new BehaviorMessage.ABuiltInOptionCaseCannotBeDeclared(name)).build();
        };
    }
}
