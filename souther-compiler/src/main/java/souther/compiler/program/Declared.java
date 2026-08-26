package souther.compiler.program;

/**
 * What {@link CheckedProgram#declaration} answers: what a value of the data an identity names is
 * made of, and who declared it.
 *
 * <p>One answer and not two questions. Every declaration this compile resolved is here — its own
 * modules', the language's, and those of the modules it read off the path — so which world a
 * declaration came from decides who emits it and never whether it can be laid out. A reader that
 * had to ask where a declaration was before it could ask what it is would be choosing, of every
 * identity it holds, which world to look in; and one told that a dependency's data is somewhere
 * else has been told to go and find a snapshot that was never made — what a dependency ships is an
 * artifact, and the layout in it is this compile's own reading of that artifact.
 *
 * <p>Nothing for a name nothing declares. An identity comes from a declaration world having said
 * one is at an address, so a reader that assembled one from two strings is asking about something
 * that is not a declaration — {@link CheckedProgram#declaration} refuses rather than answering, for
 * the reason {@link CheckedData.Product#positionOf} does. A case for it would be an output handling
 * a mistake of its own as one of the states a checked program is in.
 */
public record Declared(CheckedData data, DeclaredBy declaredBy) {

    public Declared {
        if (data == null || declaredBy == null) {
            throw new IllegalArgumentException(
                    "a declaration is what it is made of and who declared it");
        }
    }
}
