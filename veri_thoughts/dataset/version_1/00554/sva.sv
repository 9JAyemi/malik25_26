// SVA for sky130_fd_sc_ms__a221o: X = (A1 & A2) | (B1 & B2) | C1
// Bind this module to the DUT. Provide a clock/reset from TB.
// If no reset is available, tie rst_n to 1'b1.

module sky130_fd_sc_ms__a221o_sva (input logic clk, input logic rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Recomputed terms and knownness
  wire a_and_calc = (A1 & A2);
  wire b_and_calc = (B1 & B2);
  wire y_calc     = a_and_calc | b_and_calc | C1;

  wire known_a = !$isunknown({A1, A2});
  wire known_b = !$isunknown({B1, B2});
  wire known_c = !$isunknown(C1);
  wire known_in = known_a & known_b & known_c;

  // Functional equivalence when inputs known
  assert property (known_in |-> (X === y_calc))
    else $error("a221o func mismatch: X != (A1&A2)|(B1&B2)|C1");

  // Internal net checking
  assert property (known_a |-> (and1_out   === a_and_calc))
    else $error("and1_out != A1&A2");
  assert property (known_b |-> (and0_out   === b_and_calc))
    else $error("and0_out != B1&B2");
  assert property ((known_a && known_b && known_c) |-> (or0_out_X === (and1_out | and0_out | C1)))
    else $error("or0_out_X != and1_out|and0_out|C1");
  assert property (X === or0_out_X)
    else $error("buf mismatch: X != or0_out_X");

  // Knownness: no X/Z on outputs when inputs known
  assert property (known_in |-> !$isunknown({and1_out, and0_out, or0_out_X, X}))
    else $error("Unknown on outputs with known inputs");

  // Dominance/implication checks
  assert property (C1 === 1'b1 |-> X === 1'b1)
    else $error("C1=1 must force X=1");
  assert property ((a_and_calc === 1'b1) |-> X === 1'b1)
    else $error("A-path true must force X=1");
  assert property ((b_and_calc === 1'b1) |-> X === 1'b1)
    else $error("B-path true must force X=1");
  assert property (known_in && (C1===1'b0) && (a_and_calc===1'b0) && (b_and_calc===1'b0) |-> (X===1'b0))
    else $error("All terms false must force X=0");

  // Coverage: key activation cases and toggles
  cover property (known_in && (C1===1)   && (a_and_calc===0) && (b_and_calc===0) && (X===1)); // C-only
  cover property (known_in && (C1===0)   && (a_and_calc===1) && (b_and_calc===0) && (X===1)); // A-only
  cover property (known_in && (C1===0)   && (a_and_calc===0) && (b_and_calc===1) && (X===1)); // B-only
  cover property (known_in && (C1===1)   && (a_and_calc===1) && (b_and_calc===1) && (X===1)); // all high
  cover property (known_in && (C1===0)   && (a_and_calc===0) && (b_and_calc===0) && (X===0)); // all low

  cover property ($rose(X));
  cover property ($fell(X));
  cover property ($rose(A1)); cover property ($fell(A1));
  cover property ($rose(A2)); cover property ($fell(A2));
  cover property ($rose(B1)); cover property ($fell(B1));
  cover property ($rose(B2)); cover property ($fell(B2));
  cover property ($rose(C1)); cover property ($fell(C1));
endmodule

// Example bind (from testbench or a package):
// bind sky130_fd_sc_ms__a221o sky130_fd_sc_ms__a221o_sva u_sva ( .clk(tb_clk), .rst_n(tb_rst_n) );