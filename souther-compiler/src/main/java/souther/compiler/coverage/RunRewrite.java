package souther.compiler.coverage;

/**
 * One rewrite a run of the classes can be asked for, and what the run asks them.
 *
 * <p>Sealed over the two families the classes carry: an arm answering as a sibling, and a walk
 * rewritten. Whoever runs a row under a rewrite holds one of these and asks {@link #asked}; whoever
 * says which rewrite it was asks which of the two it is.
 */
public sealed interface RunRewrite permits ArmReplacements.Rewrite, WalkRewrites.Rewrite {

    /** What a run under this rewrite asks the classes for, at every site it stands at. */
    Rewriting asked();
}
