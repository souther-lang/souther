package souther.compiler.check;

import java.util.Objects;

/**
 * Leave to go and read one definition of another module, and which one.
 *
 * <p>Whether a module hands a definition over is a fact about that module: it declared the
 * definition, it wrote a body here rather than leaving one to be supplied, and it exposed the name.
 * That is settled where a module becomes a reading ({@link ModuleUniverse.InSight.Read}), and this
 * is what a reading answers with when it says yes.
 *
 * <p>Written as a value rather than left as a {@code boolean} because of what happens after the
 * answer. Reading another module's bodies is a thing some passes have to do — a published helper is
 * expanded at the call, so the body has to arrive — and the pass that does it holds the other
 * module's whole tree while it works. Told only "yes" and left holding the tree, it may reach the
 * body under a name nothing agreed to hand over, and the next reader of the same tree may work the
 * rule out again and get a different answer. That is how the rule came to be written twice, once
 * over each representation.
 *
 * <p>So the body is reached through this and not through a name. Holding another module's tree is
 * one capability and deciding what may be taken from it is another, and the second is not implied
 * by the first: a pass with the tree and no leave has nothing it may read.
 *
 * <p>Made nowhere else. The constructor is package-private, so a reading is the only thing that can
 * say a definition is published — a pass outside this package cannot write one for itself, whatever
 * it believes about the module it is holding.
 */
public final class PublishedHelper {

    private final String module;
    private final String name;

    PublishedHelper(String module, String name) {
        this.module = Objects.requireNonNull(module, "the module that publishes it");
        this.name = Objects.requireNonNull(name, "what it is declared as there");
    }

    /** The module that publishes it, under the name it declared. */
    public String module() {
        return module;
    }

    /** What it is declared as there, which is also what a reader writes for it. */
    public String name() {
        return name;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof PublishedHelper published
                && module.equals(published.module) && name.equals(published.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(module, name);
    }

    @Override
    public String toString() {
        return module + "." + name;
    }
}
