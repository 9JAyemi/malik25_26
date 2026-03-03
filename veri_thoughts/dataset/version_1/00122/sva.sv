// SVA bind checker for Mult4x4
// Concise, high-quality checks and coverage for correctness, structure, and X-prop

module Mult4x4_sva
(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [7:0] Result,
  input  logic [5:0] wResInt1,
  input  logic [5:0] wResInt2
);

  // Event to sample on any combinational change
  event comb_ev; always @* -> comb_ev;

  // Helpers
  function automatic logic [7:0] full_mul (logic [3:0] a, logic [3:0] b);
    return a * b;
  endfunction
  function automatic logic [5:0] pp_lo (logic [3:0] a, logic [1:0] bl);
    return a * bl;
  endfunction
  function automatic logic [5:0] pp_hi (logic [3:0] a, logic [1:0] bh);
    return a * bh;
  endfunction

  // 1) X/Z propagation control
  a_no_xz_inputs: assert property (@(comb_ev) !$isunknown({A,B}))
    else $error("Mult4x4: X/Z on inputs A,B");

  a_no_xz_output_when_inputs_known: assert property (@(comb_ev)
      (!$isunknown({A,B})) |-> !$isunknown(Result))
    else $error("Mult4x4: Output Result is X/Z with known inputs");

  // 2) Internal partial products match intent
  a_pp_match: assert property (@(comb_ev)
      (!$isunknown({A,B})) |-> (wResInt1 == pp_lo(A,B[1:0]) && wResInt2 == pp_hi(A,B[3:2])))
    else $error("Mult4x4: Partial product mismatch");

  // 3) Structural sum wiring (zero-extend partials to 8b before shifting/adding)
  a_structural_sum: assert property (@(comb_ev)
      (!$isunknown({A,B})) |-> (Result == (({2'b00,wResInt2} << 2) + {2'b00,wResInt1})))
    else $error("Mult4x4: Structural sum != Result");

  // 4) Functional correctness: full 4x4 multiply must match
  a_functional_correctness: assert property (@(comb_ev)
      (!$isunknown({A,B})) |-> (Result == full_mul(A,B)))
    else $error("Mult4x4: Result != A*B");

  // 5) Detect loss due to left-shift truncation of wResInt2 (design risk)
  a_no_trunc_in_hi_pp_shift: assert property (@(comb_ev)
      (!$isunknown({A,B})) |-> (wResInt2[5:4] == 2'b00))
    else $error("Mult4x4: High partial has nonzero bits lost by <<2 (potential overflow/truncation)");

  // 6) Key functional coverage (concise but meaningful)
  c_zero_zero:       cover property (@(comb_ev) (A==4'd0 && B==4'd0 && Result==8'd0));
  c_max_max:         cover property (@(comb_ev) (A==4'd15 && B==4'd15));
  c_lo_bits_all0:    cover property (@(comb_ev) (B[1:0]==2'd0));
  c_lo_bits_all1:    cover property (@(comb_ev) (B[1:0]==2'd1));
  c_lo_bits_all2:    cover property (@(comb_ev) (B[1:0]==2'd2));
  c_lo_bits_all3:    cover property (@(comb_ev) (B[1:0]==2'd3));
  c_hi_bits_all0:    cover property (@(comb_ev) (B[3:2]==2'd0));
  c_hi_bits_all1:    cover property (@(comb_ev) (B[3:2]==2'd1));
  c_hi_bits_all2:    cover property (@(comb_ev) (B[3:2]==2'd2));
  c_hi_bits_all3:    cover property (@(comb_ev) (B[3:2]==2'd3));
  c_trunc_exercised: cover property (@(comb_ev) (wResInt2[5:4] != 2'b00)); // scenario that would lose bits on <<2

  // A few corner operand covers
  c_A_edges0:        cover property (@(comb_ev) (A==4'd0));
  c_A_edges1:        cover property (@(comb_ev) (A==4'd1));
  c_A_edgesF:        cover property (@(comb_ev) (A==4'd15));

endmodule

// Bind to all instances of Mult4x4; internal wires are connected by name
bind Mult4x4 Mult4x4_sva sva_i (.*);