// SVA for nor4b_4_input
module nor4b_4_input_sva (
  input logic A, B, C, D_N,
  input logic Y
);

  // Functional equivalence (combinational, clockless)
  a_func: assert property (Y === ~(A | B | C | D_N))
    else $error("nor4b_4_input mismatch: Y=%b, in=%b", Y, {A,B,C,D_N});

  // No X on output when inputs are known
  a_known: assert property (!$isunknown({A,B,C,D_N}) |-> !$isunknown(Y))
    else $error("Y unknown while inputs are known: in=%b", {A,B,C,D_N});

  // No glitching: if inputs stable, output stable
  a_glitchfree: assert property ($stable({A,B,C,D_N}) |-> $stable(Y))
    else $error("Glitch detected: Y changed without input change");

  // Useful corner-case checks
  a_all_zero_high: assert property ((!A && !B && !C && !D_N) |-> (Y===1'b1))
    else $error("All-zero inputs did not produce Y=1");
  a_any_one_low:  assert property ((A||B||C||D_N) |-> (Y===1'b0))
    else $error("Any-one input did not force Y=0");

  // Output toggle coverage
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Full input-space coverage (all 16 combinations)
  covergroup cg_inputs @( {A,B,C,D_N} );
    coverpoint {A,B,C,D_N} { bins all[] = {[4'b0000:4'b1111]}; }
  endgroup
  cg_inputs cg = new();

endmodule

// Bind into DUT
bind nor4b_4_input nor4b_4_input_sva u_nor4b_4_input_sva (
  .A(A), .B(B), .C(C), .D_N(D_N), .Y(Y)
);