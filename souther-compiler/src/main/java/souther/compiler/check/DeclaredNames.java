package souther.compiler.check;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Which of the declarations a module writes it actually has, and one refusal per declaration it may
 * not.
 *
 * <p>A name declared twice keeps the first: the second is refused and left out, so the rest of the
 * module still means what it means. Writing a declaration twice is what copying one looks like
 * halfway through, and taking every name in the file away until it is finished is the opposite of
 * useful.
 *
 * <p>Written over the names rather than over a tree, because the rule is the same one on both sides
 * of {@code Resolve}: which declarations a module has is settled by what it wrote, and nothing about
 * it is a question resolution answers. Both representations ask it here so that the two cannot come
 * to differ about what a module declares.
 *
 * <p>What comes back is a fact and not a report. A refusal says which declaration is refused and
 * which rule refused it, and that is all it says — where to complain about it, and whether there is
 * anyone to complain to, depend on where the declarations came from. A module of this compilation
 * has an author holding the file; a module read back off an artifact has nobody, and a rule broken
 * inside one is a fact about what the artifact carries. Minting a diagnostic here made those one
 * answer, and the second was reached by catching an exception type.
 */
public final class DeclaredNames {

    private DeclaredNames() {
    }

    /**
     * What a module declares, keyed by the name written there, and the declarations it may not have.
     *
     * <p>Partial on purpose. The declarations are what is left after the refusals are taken out, so
     * a reader that has a source to report against goes on with them and reports the rest. A reader
     * with nowhere to report has an index it may not use at all unless {@link #refusals()} is empty,
     * and that is the reader's own rule rather than something read off this.
     */
    public record Index<D>(Map<String, D> declarations, List<Refusal<D>> refusals) {

        public Index {
            declarations = Collections.unmodifiableMap(new LinkedHashMap<>(declarations));
            refusals = List.copyOf(refusals);
        }
    }

    /**
     * One declaration a module writes and does not have, as which rule refused it.
     *
     * <p>Closed, so that a reader turning these into something else — a report, a fact about an
     * artifact, a fault — says what it does about each. A rule added here is one every such reader
     * has to have an answer for, and the compiler asks them for it.
     */
    public sealed interface Refusal<D> {

        /** The declaration this is about. */
        D refused();

        /** The name is already declared by this module, and the first one keeps it. */
        record DeclaredTwice<D>(D refused) implements Refusal<D> {}

        /**
         * It is named after a built-in {@code Option} case.
         *
         * <p>{@code Some} and {@code None} are the built-in cases (ADR-0011); a user data of the
         * same name would make a {@code | Some v} pattern ambiguous between {@code Option} and the
         * user case, so the declaration is refused rather than allowed to collide (ADR-0035).
         */
        record ABuiltInOptionCaseIsDeclared<D>(D refused) implements Refusal<D> {}
    }

    /** What {@code defs} declares, by the name each is written under. */
    public static <D> Index<D> index(List<D> defs, Function<D, String> name) {
        Map<String, D> declared = new LinkedHashMap<>();
        List<Refusal<D>> refused = new ArrayList<>();
        for (D def : defs) {
            String bare = name.apply(def);
            if (bare.equals("Some") || bare.equals("None")) {
                refused.add(new Refusal.ABuiltInOptionCaseIsDeclared<>(def));
                continue;
            }
            if (declared.containsKey(bare)) {
                refused.add(new Refusal.DeclaredTwice<>(def));
                continue;
            }
            declared.put(bare, def);
        }
        return new Index<>(declared, refused);
    }
}
