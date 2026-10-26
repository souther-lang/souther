package souther.compiler.execute;

import java.util.List;

/**
 * A value a module declares, asked whether building it breaks an invariant.
 *
 * <p>A value takes nothing of a caller and is built once, where its module builds it, so what is
 * asked is the module, the name, and the values the module's own build hands it. The answer is the
 * program's: the value is built by the code that ships, and what happens is what the language would
 * have done when the module was built.
 *
 * <p>A value that reads another is built from that other, which the region that builds it has built
 * already and hands over. Asked here the same way: the values it is handed are built first and in
 * the order they are handed, each as a value of its own, so an invariant broken by one of them is
 * the answer for the one that reads it.
 *
 * @param writtenIn the module the value is declared in, which is the compile whose classes it is
 *                  built from
 * @param name      the value, as the module declares it
 * @param handedOver the values the build of this one is handed, in the order it is handed them
 */
public record BuiltValue(String writtenIn, String name, List<BuiltValue> handedOver) {

    public BuiltValue {
        if (writtenIn == null || writtenIn.isEmpty() || name == null || name.isEmpty()) {
            throw new IllegalArgumentException("a value is some module's and has a name: "
                    + writtenIn + "." + name);
        }
        handedOver = List.copyOf(handedOver);
    }
}
