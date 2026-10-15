package souther.compiler.inputs;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * Which values' rules reach the positions of an input, for a reader that composes a value at them.
 *
 * <p>The roots {@link InputDomain} opened, and nothing worked out beside them. Which value's rules
 * hold a position is settled where the descent opens a reading — narrowing into a case, entering
 * what a container holds — and a composer that worked it out again from the shape of what it is
 * building would have a second answer to that question, right for as long as every value it builds
 * is the parameter's own record.
 *
 * <p>Kept as the roots and compared as them, for the reason the domain keeps them that way: what a
 * composer is handed is part of an answer, and an answer is compared as a value.
 */
public record RuleRoots(List<InputDomain.RuleRoot> roots) {

    public RuleRoots {
        roots = List.copyOf(roots);
    }

    /**
     * One value whose rules name a position, and the name.
     *
     * @param address which value's rules, and what they call the position
     * @param value   what that value is declared to be, which is what its rules are read off
     */
    public record Naming(RuleAddress address, Type value) {}

    /**
     * Every value whose rules name {@code path}, innermost first.
     *
     * <p>The innermost is the deepest root whose rules can name the position at all: a case's rules
     * name its own fields, an element's rules its own, and a parameter's rules every field it
     * reaches through fields alone. Past it, a case hands a name every case shares to the value
     * above, which calls it with the narrowing taken out ({@link SharedNames#outerPathOf}); an
     * element hands nothing on, since what the value above says of a container it says of the
     * container and not of what stands in it.
     *
     * <p>Every value named here holds wherever a value stands at {@code path}. A case is on the way
     * to the position only where the value turned out to be that case, and an element only where
     * the container holds one — so a position under one case is never named by another case's rules,
     * and an empty container is never held to what its elements would have to be.
     */
    public List<Naming> naming(TermPath path) {
        List<Naming> out = new ArrayList<>();
        TermPath here = path;
        while (here != null) {
            InputDomain.RuleRoot innermost = null;
            RuleAddress named = null;
            for (InputDomain.RuleRoot root : roots) {
                RuleAddress address = RuleAddress.of(root.at(), here);
                if (address != null && (innermost == null
                        || root.at().steps().size() > innermost.at().steps().size())) {
                    innermost = root;
                    named = address;
                }
            }
            if (innermost == null) {
                break;
            }
            out.add(new Naming(named, innermost.type()));
            here = innermost.opening() instanceof RootOpening.Refined(var _, SharedNames crossing)
                    ? crossing.outerPathOf(here) : null;
        }
        return List.copyOf(out);
    }
}
