package souther.compiler.check;

import souther.compiler.ast.WrittenName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.DataMessage;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Which of the declarations a module writes it actually has, and one error per declaration it may
 * not.
 *
 * <p>A name declared twice keeps the first: the second is reported and left out, so the rest of the
 * module still means what it means. Writing a declaration twice is what copying one looks like
 * halfway through, and taking every name in the file away until it is finished is the opposite of
 * useful.
 *
 * <p>Written over the names and positions rather than over a tree, because the rule is the same one
 * on both sides of {@code Resolve}: which declarations a module has is settled by what it wrote, and
 * nothing about it is a question resolution answers. Both representations ask it here so that the
 * two cannot come to differ about what a module declares.
 */
public final class DeclaredNames {

    private DeclaredNames() {
    }

    /** What a module declares, keyed by the name written there, and the errors for the rest. */
    public record Of<D>(Map<String, D> defs, List<CompileException> rejected) {}

    public static <D> Of<D> of(List<D> defs, Function<D, String> name, Function<D, WrittenName> written,
                        Function<D, SourcePos> pos) {
        Map<String, D> declared = new LinkedHashMap<>();
        List<CompileException> rejected = new ArrayList<>();
        for (D def : defs) {
            String bare = name.apply(def);
            if (bare.equals("Some") || bare.equals("None")) {
                // Some/None are the built-in Option cases (ADR-0011); a user data of the same name
                // would make a `| Some v` pattern ambiguous between Option and the user case, so the
                // declaration is rejected here rather than allowed to collide (ADR-0035).
                rejected.add(CompileException.of(Diagnostic
                        .at(written.apply(def).reportedAt())
                        .say(new BehaviorMessage.ABuiltInOptionCaseCannotBeDeclared(bare)).build()));
                continue;
            }
            if (declared.containsKey(bare)) {
                rejected.add(CompileException.of(Diagnostic
                        .at(pos.apply(def))
                        .say(new DataMessage.ADataIsAlreadyDefined(bare)).build()));
                continue;
            }
            declared.put(bare, def);
        }
        return new Of<>(declared, List.copyOf(rejected));
    }
}
