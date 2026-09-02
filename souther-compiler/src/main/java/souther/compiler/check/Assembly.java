package souther.compiler.check;

/**
 * Parts joined, carrying no claim about them.
 *
 * <p>Said here because nothing about the shape of a class says it. A state of this package — a
 * module that has had the cycle check run over it, one whose invariants are settled — is a final
 * class nobody outside can build, reached only through the operation that establishes what it
 * claims. An assembly is written the same way and claims nothing: it holds the parts a reader needs
 * beside each other, and what each part is worth was established where the part was made.
 *
 * <p>Which of the two a class is decides what may be asked of it, so it is written down rather than
 * guessed at. A reading that told them apart by their shape would call every assembly a state, and
 * a rule about states failing on one would leave nobody able to say whether the rule was broken or
 * the class was never a state to begin with.
 *
 * <p>Sealed, so that the set is what somebody decided rather than what a class happened to look
 * like. A final class of this package that is not here is a state and is held to what a state is
 * held to, which is the way round that fails loudly.
 */
public sealed interface Assembly permits CheckSurface {
}
