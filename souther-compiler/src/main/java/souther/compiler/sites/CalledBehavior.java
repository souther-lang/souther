package souther.compiler.sites;

import souther.compiler.diag.Region;

import java.util.List;

/**
 * A behavior a call reaches, and what its declaration says it takes.
 *
 * <p>The names come from the declaration and not from the call: a behavior declares named
 * parameters, and what a reader writing an argument wants to know is which of those they are
 * writing. What the call put there is what they are looking at.
 *
 * <p>Which argument is being written is not here. That is counted in the source the author left, and
 * a source finished off for them would count a bracket nobody typed.
 *
 * <p>{@code writtenAt} is where the name reaching this behavior is written, which is the whole of a
 * qualified one. A caller reading a source finished off for an author has to know how far into it an
 * answer reaches, and cannot work that out from a call: a call runs to its closing bracket, and that
 * bracket may be one nobody typed.
 */
public record CalledBehavior(String name, List<Takes> takes, Region writtenAt) {

    /** One parameter of the declaration: what it is called, and what arrives there. */
    public record Takes(String name, TypeFact type) {}
}
