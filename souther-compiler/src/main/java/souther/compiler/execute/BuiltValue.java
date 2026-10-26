package souther.compiler.execute;

/**
 * A value a module declares, asked whether building it breaks an invariant.
 *
 * <p>A value takes nothing and is built once, where its module builds it, so what is asked is the
 * module and the name and nothing the run would have to be handed. The answer is the program's: the
 * value is built by the code that ships, and what happens is what the language would have done
 * when the module was built.
 *
 * @param writtenIn the module the value is declared in, which is the compile whose classes it is
 *                  built from
 * @param name      the value, as the module declares it
 */
public record BuiltValue(String writtenIn, String name) {

    public BuiltValue {
        if (writtenIn == null || writtenIn.isEmpty() || name == null || name.isEmpty()) {
            throw new IllegalArgumentException("a value is some module's and has a name: "
                    + writtenIn + "." + name);
        }
    }
}
