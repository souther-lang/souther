package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Where the modules a module is resolved against come from.
 *
 * <p>One question, asked by name. That is the whole of it: a universe says what it has under a name
 * and nothing about what a name written in a module means. What names mean is {@link Scoping}'s,
 * and it is the same rule whichever universe answered — a compilation reading its own sources, or a
 * reader putting a set of published classes back together.
 *
 * <p>Two universes assembling a scope apiece is what left a model that compiles in the project that
 * wrote it and refuses to be imported anywhere else: the two agreed on nothing but by having been
 * written to agree, and a rule changed on one side stayed right on the other. So there is nothing
 * here to derive a scope with. What can be worked out from a module is worked out once, where the
 * scope is assembled.
 *
 * <p>Asked one name at a time rather than handed over as a set, because a compilation that reaches
 * no other module reads none.
 *
 * <p>What it answers is what may be built on, and that is the whole of what it answers. A universe
 * that will not let a module be built on says nothing further about it — not its text, not the
 * behaviors it declares — so a reader here does not have to know which of several questions to ask
 * to get the most that can be had. The cost falls where it should: every module answered that way
 * is one already refused for a reason its author has been given, and what is lost is a second
 * report about it.
 *
 * <p>It is worth knowing that a compilation refuses one on grounds that are not about the module at
 * all. A module in an import cycle has been read, and what stops it is a rule about the set it is
 * in; that rule is written into what a compilation says a module declares, so it arrives here.
 * Whether it belongs there is its own question and not one this seam settles.
 */
public interface ModuleUniverse {

    /** What this universe has under {@code name}. */
    InSight module(String name);

    /**
     * What a universe has under a name.
     *
     * <p>Three answers and not two. Knowing a name and being able to read what it declares are
     * different things, and a reader told only whether a module came back cannot tell an import of
     * something that is not there — which is the importer's mistake and is reported on the import
     * line — from an import of something that is there and cannot be read, whose fault is reported
     * on its own source and would be said twice if it were said here as well.
     */
    sealed interface InSight {

        /**
         * What a universe says a module is, to a module that names it: everything one module may
         * observe of another, and nothing else.
         *
         * <p>Settled here and not read off the module afterwards. What it declares is a rule and
         * not a reading — a name written twice keeps the first, a built-in case name is refused —
         * and a reader that indexed the declarations itself would be a second place that rule is
         * written, the two differing in what they do about the ones they refuse. The same holds of
         * every other fact one module needs of another: what it exposes, which behaviors it
         * declares, which of its definitions it publishes. Each of those was worked out by whoever
         * wanted it, off {@code exposing} and {@code behaviors} and {@code fns}, and the readers
         * disagreed — a behavior arrived under an import line that was refused, because the walk
         * that decided the value namespace never asked whether the module exposed it.
         *
         * <p>So this holds no module. A reader that could reach one could work the same facts out
         * again, and "it does not today" is not a rule. What is here is what was settled, asked one
         * name at a time: a question answered is a question a reader cannot answer differently.
         *
         * <p>What a module's own import lines let it write bare is not here. It is not something
         * one module needs of another — nothing a reader writes is answered by the library names
         * another module may write bare — and reading it of every module named would put every
         * importer's scope behind an edit to a line in a module it imports from. It belongs to the
         * module being scoped, and travels with it ({@link Scoping.Subject}).
         */
        final class Read implements InSight {

            private final String module;
            private final Registry.Declared<Ast.Def> declared;
            private final Set<String> behaviors;
            private final Set<String> values;
            private final Set<String> publishedHelpers;

            private Read(String module, Registry.Declared<Ast.Def> declared,
                         Set<String> behaviors, Set<String> values,
                         Set<String> publishedHelpers) {
                this.module = module;
                this.declared = declared;
                this.behaviors = Collections.unmodifiableSet(new LinkedHashSet<>(behaviors));
                this.values = Set.copyOf(values);
                this.publishedHelpers = Set.copyOf(publishedHelpers);
            }

            /**
             * The one place a module's observable semantics are worked out.
             *
             * <p>Handed the module and the declarations something already indexed, because those
             * two are settled elsewhere and by different rules: what a module wrote is the parse,
             * and which of its declarations it has is {@link DeclaredNames}' to say, at the
             * boundary where there is still somebody to report a refusal to. Everything else one
             * module may observe of another is derived here, once, and the module is not kept.
             */
            public static Read of(Ast.Module module, Registry.Declared<Ast.Def> declared) {
                Set<String> behaviors = Scoping.behaviorNames(module);
                Set<String> exposed = declared.exposed();
                Set<String> values = new LinkedHashSet<>();
                Set<String> published = new LinkedHashSet<>();
                for (Ast.FnDef fn : module.fns()) {
                    if (!HelperInliner.isHelperName(behaviors, fn.name())) {
                        continue;   // a behavior's `let` is its implementation, not a name of its own
                    }
                    values.add(fn.name());
                    if (HelperInliner.publishes(exposed, fn.name(),
                            fn.body() instanceof Ast.FnBody.Written, List.of(fn.name()))) {
                        published.add(fn.name());
                    }
                }
                return new Read(module.name(), declared, behaviors, values, published);
            }

            /**
             * The declaration of that name, or null where it declares none.
             *
             * <p>Asked one name at a time, and there is no way to ask for them all. A reader that
             * held the index could sort the declarations into behaviors and values and types for
             * itself, which is the rule this exists to keep in one place — the same reason the
             * names a report may offer are a capability of their own ({@link
             * #behaviorNamesToSuggest}) rather than the set this is read from. The module being
             * scoped reads its own index, from {@link Scoping.Subject}, because reading itself is
             * what a subject is.
             */
            public Ast.Def declaration(String name) {
                return declared.declarations().get(name);
            }

            /** Whether the module offers that name to a reader at all. */
            public boolean exposes(String name) {
                return declared.exposed().contains(name);
            }

            /** Whether it declares a behavior of that name. */
            public boolean declaresBehavior(String name) {
                return behaviors.contains(name);
            }

            /** Whether it declares a value of that name — a {@code let} that is not a behavior's
             *  implementation. Neither this nor a behavior is a data, so an import of one reaches
             *  the value namespace and nothing in the type namespace answers for it. */
            public boolean declaresValue(String name) {
                return values.contains(name);
            }

            /**
             * Leave to read the definition of that name, where the module hands one over: exposed,
             * and with a body written here rather than left to be supplied.
             *
             * <p>The answer is the leave and not a {@code boolean}, because what follows a yes is
             * another module's body being read. {@link PublishedHelper} is what a reader shows for
             * it, and a reader that only holds the other module's tree has nothing to show.
             */
            public java.util.Optional<PublishedHelper> publishedHelper(String name) {
                return publishedHelpers.contains(name)
                        ? java.util.Optional.of(new PublishedHelper(module, name))
                        : java.util.Optional.empty();
            }

            /**
             * The behavior names a report may offer where nothing answered to one.
             *
             * <p>Apart from {@link #declaresBehavior}, though both read the same set, because they
             * are different capabilities. That one settles what a name means; this one is what a
             * "did you mean" may say, and what belongs in it is a question about reports — how near
             * a spelling has to be, whether something a reader could not reach anyway is worth
             * offering. Answered by one method, a change to either would be a change to both.
             */
            public Set<String> behaviorNamesToSuggest() {
                return behaviors;
            }

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
     * <p>Made nowhere else. It is declared inside the reading and its constructor is private, so the
     * only code that can say a definition is published is the code that settles what a module
     * publishes. Package-private would have left every class beside that one able to write a leave for
     * itself, which is a rule kept by nobody looking rather than by anything.
     */
    public static final class PublishedHelper {

        private final String module;
        private final String name;

            private PublishedHelper(String module, String name) {
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

            /** Two of these say the same thing when every fact they settled is the same. Written
             *  out because this ends up inside an answer a compilation remembers, and an answer
             *  that never equals the last one is one nothing that read it is kept past. */
            @Override
            public boolean equals(Object other) {
                return other instanceof Read read
                        && module.equals(read.module)
                        && declared.equals(read.declared)
                        && behaviors.equals(read.behaviors)
                        && values.equals(read.values)
                        && publishedHelpers.equals(read.publishedHelpers);
            }

            @Override
            public int hashCode() {
                return Objects.hash(module, declared, behaviors, values, publishedHelpers);
            }

            @Override
            public String toString() {
                return "Read[" + module + " declares=" + declared.declarations().keySet()
                        + ", exposes=" + declared.exposed() + ", behaviors=" + behaviors
                        + ", values=" + values + ", publishes=" + publishedHelpers + "]";
            }
        }

        /** This universe has it and cannot say what it declares. Whatever is wrong with it is
         *  reported where it is, so a reader that reached it says nothing further. */
        record Unreadable() implements InSight {}

        /** Nothing of that name here. */
        record Unknown() implements InSight {}

        InSight UNREADABLE = new Unreadable();
        InSight UNKNOWN = new Unknown();

        /**
         * Whether this universe has a module of that name at all, whether or not it can say what it
         * declares.
         *
         * <p>Written once, here, because it is the one question two of the three answers agree on
         * and a reader asking it for itself asks it as "not the third one" — which reads as though
         * the other two were one answer, and is how they came to be treated as one.
         */
        default boolean isThere() {
            return !(this instanceof Unknown);
        }
    }

    /**
     * The modules of a set already read. A name that is not among them is nothing this universe
     * has — a reading that went wrong is left out by whoever read it, and is
     * {@link InSight.Unreadable} only if it says so.
     *
     * <p>A record rather than a lambda, for the reason {@link Scoping.OfTheUniverse} is: a universe
     * ends up inside an answer a compilation remembers, and two answers built from the same
     * universe have to be equal or nothing that read one is ever kept.
     */
    record OfWhatIsRead(Map<String, InSight> modules) implements ModuleUniverse {

        public OfWhatIsRead {
            modules = Map.copyOf(modules);
        }

        @Override
        public InSight module(String name) {
            return modules.getOrDefault(name, InSight.UNKNOWN);
        }
    }

    /** Nothing in sight — a module resolved on its own. */
    ModuleUniverse NOTHING = new OfWhatIsRead(Map.of());
}
