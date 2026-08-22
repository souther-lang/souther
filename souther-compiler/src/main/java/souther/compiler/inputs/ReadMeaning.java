package souther.compiler.inputs;

import souther.compiler.core.Core;

/**
 * What a name a body reads stands for, said in terms of the behavior's input.
 *
 * <p>Four answers rather than two. A reader that asks only which position a name is gets a position
 * or nothing, and that nothing holds three different names at once: one given arithmetic over
 * positions, one an operation handed an element on, and one this reading knows nothing about. Told
 * apart nowhere, they were read the same way — so a rule written over a name given arithmetic drew
 * no line, and nothing said why.
 *
 * <p>Facts about the name and not permissions. Whether a reader may put {@link Through}'s expression
 * where the name stands is that reader's to settle from the fact; what is answered here is what the
 * reading of the input knows, which is the same knowledge whoever asks.
 */
public sealed interface ReadMeaning {

    /** The name is a position of the behavior's input: a place a row writes at. */
    record Position(TermPath path) implements ReadMeaning {}

    /**
     * The name and {@code value} are one value, which is what the name was given, and {@code at} is
     * what that value is read in.
     *
     * <p>What is held is the expression rather than anything read off it. Which of the readings of a
     * value this expression carries — an affine form, the positions it mentions — is each reader's
     * own question, and answering one of them here would be this reading keeping an account of a
     * name that only one reader could use.
     *
     * <p>The environment comes with it because it is part of the answer. A value stands for the name
     * in the environment the binding was made in, which is not always the one the name was read in;
     * left out, each reader supplies one, and two readers that supply different ones are two
     * accounts of what the name means — which is the shape this whole reading exists to remove.
     * Today they cannot be told apart, and what makes that one fact rather than two is that it is
     * settled here.
     */
    record Through(Core value, InputReads at) implements ReadMeaning {}

    /**
     * An operation of the language handed the name an element of a container, and no position of the
     * input holds those elements.
     *
     * <p>Which is not the same as knowing nothing. The name holds something, and what it holds is
     * one element of what an operation answered rather than the value the name has at a read — an
     * expression built from a closure's parameter, standing for every element at once. A reader that
     * put it where the name stands would state of one value what was written about all of them.
     */
    record Element() implements ReadMeaning {}

    /** Nothing in this reading gives the name a meaning: no position, no value it was given, and no
     *  operation that handed it one. */
    record Unknown() implements ReadMeaning {}
}
