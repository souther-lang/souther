package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

/**
 * What a reader may say when a declaration world answered with a declaration for an identity that
 * is not a module's.
 *
 * <p>It cannot happen. A {@code data} is written in a module, and asking the declaration world with
 * an identity the language gives answers nothing at all — so a reader that has both a
 * {@link Hir.Data} and a name that is not {@link TypeSymbol.AtModule} is holding two answers that
 * cannot both be true. Said in one place because more than one reader is in that position, and two
 * of them wording it separately is two accounts of one impossibility.
 */
final class Declared {

    private Declared() {}

    /** @throws IllegalStateException always */
    static <T> T notAModules(TypeSymbol named, Hir.Def answered) {
        throw new IllegalStateException("`" + named + "` is not a declaration a module wrote, and `"
                + answered.declares() + "` was answered for it");
    }
}
