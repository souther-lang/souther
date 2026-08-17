package souther.compiler.types;

/**
 * One case a subject can be selected as: the name it is written by, and what the value turns out to
 * be once it has been ({@link Refinement}).
 *
 * <p>A <em>selector</em> rather than a variant or a partition, because one value can satisfy more
 * than one of them. A data may be a case of two named sums declared in its module, and the classes
 * generated for it implement the interface of each, so testing two selectors of one subject can both
 * answer yes. What that means is the reader's to decide — a {@code match} takes the first arm whose
 * selector answers, a behavior's declared relation holds every rule whose selector answers — and
 * nothing here decides it for them.
 *
 * <p>The name and the carrier agree, and are made together so that they cannot disagree. An
 * optional's carriers are named by the optional's own cases and nothing else may be: a selector
 * spelled {@code Some} whose carrier were the absent one would be tested as absent and reported as
 * present, and a reader would have no way to tell which half was the mistake.
 */
public record CaseSelector(TypeSymbol name, Refinement refinement) {

    public CaseSelector {
        if (name == null || refinement == null) {
            throw new IllegalArgumentException("a selector is a name and what it refines the value to");
        }
        if (named(refinement) != null && !named(refinement).equals(name)) {
            throw new IllegalArgumentException(
                    "an optional's carrier is named by the case it is: " + name + " is not "
                            + named(refinement));
        }
        if (named(refinement) == null && (TypeSymbol.SOME.equals(name) || TypeSymbol.NONE.equals(name))) {
            throw new IllegalArgumentException("an optional's case is one of its own carriers: " + name);
        }
        // A case whose carrier is the value holds what its name says it holds. The emitter reads the
        // two apart — the name picks the class it tests, the held type says what the value is read
        // as — so a pair that disagreed would test one class and read the value as something else.
        if (refinement instanceof Refinement.Direct direct
                && !java.util.Objects.equals(direct.bound(), heldBy(name))) {
            throw new IllegalArgumentException("`" + name + "` holds " + heldBy(name)
                    + ", which is not " + direct.bound());
        }
    }

    /**
     * A case whose carrier is the value: a union member, or a case of a named sum.
     *
     * <p>What it holds is not taken from the caller. A name and the type it holds are one fact
     * written twice, and the emitter reads them apart — the name says which class is tested, the
     * bound type says what the value is read as — so a pair that disagreed would test one class and
     * read the value as something else.
     */
    public static CaseSelector direct(TypeSymbol name) {
        return new CaseSelector(name, new Refinement.Direct(heldBy(name)));
    }

    /**
     * The type a case holds when a value turns out to be it. A primitive-named case (the
     * {@code Int} of {@code Int | DivisionByZero}) holds that primitive; a data-named case holds its
     * data type.
     *
     * <p>Null where the name denotes no type. {@code Some} and {@code None} are primitive-module
     * names that denote none — an optional's carriers are made by their own factories, which know
     * the element this cannot — and neither does {@code Raw}, which no stage produces.
     */
    public static Type heldBy(TypeSymbol caseName) {
        if (!caseName.isPrimitive()) {
            return Type.ref(caseName);
        }
        // Read back through the one spelling table rather than repeating it here.
        Type.Prim prim = caseName.primitiveKind();
        return prim == null || prim == Type.Prim.RAW ? null : prim;
    }

    /** The carrier an optional holding {@code element} is. */
    public static CaseSelector optionPresent(Type element) {
        return new CaseSelector(TypeSymbol.SOME, new Refinement.OptionPresent(element));
    }

    /** The carrier an optional holding nothing is. */
    public static CaseSelector optionAbsent() {
        return new CaseSelector(TypeSymbol.NONE, new Refinement.OptionAbsent());
    }

    /** What a value selected by this is read as, or null where nothing readable stands under it. */
    public Type bound() {
        return refinement.bound();
    }

    /** The case a carrier is the one of, for the carriers that are a particular case; null for one
     *  that stands for whatever case names it. */
    private static TypeSymbol named(Refinement refinement) {
        return switch (refinement) {
            case Refinement.Direct ignored -> null;
            case Refinement.OptionPresent ignored -> TypeSymbol.SOME;
            case Refinement.OptionAbsent ignored -> TypeSymbol.NONE;
        };
    }
}
