/**
 * The boundary a derived decoder and encoder stand on (spec {@code [#codec-generation]},
 * {@code [#jvm-codec]}): what a decode answers ({@link souther.runtime.boundary.Refusals}), what it
 * reads its input through ({@link souther.runtime.boundary.TreeReader}), and the parts a derived
 * codec is generated from ({@link souther.runtime.boundary.Decoding},
 * {@link souther.runtime.boundary.Encoding}).
 *
 * <p>Nothing here names a decoder library. A decoder binding adapts one to these types from outside,
 * and decides nothing about what a decode admits (spec {@code [#decoder-binding]}).
 */
@NullMarked
package souther.runtime.boundary;

import org.jspecify.annotations.NullMarked;
