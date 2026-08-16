package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.Diagnostic;
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
 * <p>One place for each rule's sentence, and a switch with nothing to fall through to: a rule added
 * to the indexing is one this has to have a sentence for.
 */
public final class DeclarationRefusals {

    private DeclarationRefusals() {
    }

    /** How {@code refusal} is said to the author of the module that wrote it. */
    public static Diagnostic reported(DeclaredNames.Refusal<Ast.Def> refusal) {
        Ast.Def def = refusal.refused();
        return switch (refusal) {
            case DeclaredNames.Refusal.DeclaredTwice<Ast.Def> _ -> Diagnostic
                    .at(def.pos())
                    .say(new DataMessage.ADataIsAlreadyDefined(def.name())).build();
            case DeclaredNames.Refusal.ABuiltInOptionCaseIsDeclared<Ast.Def> _ -> Diagnostic
                    .at(def.written().reportedAt())
                    .say(new BehaviorMessage.ABuiltInOptionCaseCannotBeDeclared(def.name())).build();
        };
    }
}
