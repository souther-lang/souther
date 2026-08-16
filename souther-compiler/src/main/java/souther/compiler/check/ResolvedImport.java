package souther.compiler.check;

/**
 * What one spelling an import line named turned out to mean here.
 *
 * <p>Settled in three steps, and they are three because each answers a different question. Whether
 * a claim stands at all is about the module it names: it exposes the name or it does not, it
 * declares one or it does not, and a line that names a module nothing has claims nothing. Which of
 * the standing claims is adopted is about the claims: one spelling means one thing, so two lines
 * bringing different things leave the spelling meaning neither. And what the subject's own
 * declarations do to that is about neither — a definition written here takes the spelling in the
 * namespace it is in, whatever a line said.
 *
 * <p>The third step is why {@link Held} is here rather than folded into the answer. A data brought
 * in under a spelling this module writes a {@code let} for is one arrival in two namespaces: the
 * {@code let} takes it as a value and the data is still what the type means, so a field written
 * with that type is not a second thing said about the line already refused. One answer for both
 * namespaces cannot say that.
 */
public sealed interface ResolvedImport {

    /** What the subject's own declarations already hold under this spelling. */
    Held held();

    /** One claim stood, or several stood and brought the same thing. */
    record Brings(Scoping.Brought what, Held held) implements ResolvedImport {}

    /**
     * Claims were made and none is adopted — every one of them failed, or two of them brought
     * different things and neither may have the spelling.
     *
     * <p>The spelling is in scope meaning nothing rather than being absent from it. What is wrong
     * was said on the line, so a use of it says nothing more; left out, every use would be reported
     * as a name nothing declares, and the author would be sent to a body where nothing is wrong.
     */
    record BringsNothing(Held held) implements ResolvedImport {}

    /**
     * Which namespaces the subject's own declarations occupy under this spelling.
     *
     * <p>Both, for a data written here. The value one alone for a {@code let} or a behavior, which
     * is what makes the two facets come apart. Neither, for a spelling the module does not write.
     */
    record Held(boolean asAType, boolean asAValue) {

        static final Held NOTHING = new Held(false, false);
    }
}
