package souther.compiler.codegen;

import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A class of this module building a behavior another module declares: what it hands the behavior's
 * implementation, and the constructor it links against to do it.
 *
 * <p>What the bytecode assumed and nothing else. It is written down where the instruction that links
 * the constructor is emitted, from what that instruction pushes and the descriptor it carries, so it
 * cannot be a second answer to what the class was built against. Both halves are needed: the
 * descriptor says which constructor links, and two dependencies each held as the unary
 * {@code Behavior} leave it the same whichever of them is passed where — so a behavior now taking
 * another dependency, or the same two in the other order, links and is handed the wrong one. A module
 * read off the path is held to these where it is taken into a compilation.
 *
 * @param target       the behavior being built
 * @param dependencies what it is handed, in the order the constructor takes them
 * @param constructor  the descriptor of the constructor linked against, as the JVM writes it
 */
public record ConstructionLink(ValueName.Behavior target, List<ValueName.Behavior> dependencies,
                               String constructor) {

    public ConstructionLink {
        dependencies = List.copyOf(dependencies);
    }
}
