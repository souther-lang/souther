package souther.compiler.sites;

import souther.compiler.types.Type;

/**
 * A type something outside the compiler is told, and what read it.
 *
 * <p>The pair rather than the type. A reader that is handed a type alone cannot tell what it is
 * entitled to do with it, and the two things this carries are entitled to different treatment: a
 * declared type holds of every use of the declaration, and a checked one holds of the elaboration it
 * was read from.
 *
 * <p>An open variable one application left behind may not cross. {@code Type.MetaVar} stands for the
 * type a single call settles on and is rewritten as soon as something says what that is; it lives no
 * longer than the elaboration that made it, and no answer the compiler stores holds one. So one
 * arriving here is a fact taken from the middle of an elaboration, and it is refused rather than
 * shown — a reader would render an internal spelling and mean nothing by it.
 *
 * <p>{@code Type.Var} is not refused. It is what a declaration wrote and every use of the
 * declaration holds for it, so it is a type to say. That it should not be shown under the spelling
 * the compiler minted for an inferred one is a separate rule and belongs to whatever renders it.
 */
public record TypeFact(Type type, Evidence evidence) {

    public TypeFact {
        if (type == null || evidence == null) {
            throw new IllegalArgumentException("a type fact is a type and what read it");
        }
        if (holdsAMetaVar(type)) {
            throw new IllegalArgumentException(
                    "a variable one application left open does not leave it: " + type);
        }
    }

    /**
     * Whether {@code type} holds a variable an application left open, anywhere inside it.
     *
     * <p>Anywhere: a list of them, a function answering one, a pair holding one. A check that read
     * only the outside would pass every shape that carries one, which is most of the shapes an
     * elaboration builds.
     *
     * <p>Down the children the type itself says it has. Which positions a compound holds is written
     * once, in {@code Type}, and a walk of its own here would be a second list to keep in step — the
     * one that forgot the position a constructor gained would let one through.
     */
    private static boolean holdsAMetaVar(Type type) {
        if (type instanceof Type.MetaVar) {
            return true;
        }
        boolean[] found = {false};
        Type.forEachChild(type, child -> found[0] |= holdsAMetaVar(child));
        return found[0];
    }
}
