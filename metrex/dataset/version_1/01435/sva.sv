// SVA for four_bit_adder
// Bind this file to the DUT: bind four_bit_adder four_bit_adder_sva sva (.*);

module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic       reset,
  input  logic [3:0] Sum,
  input  logic       Cout
);

  // Basic sanity (no X/Z on sample events)
  ap_no_x_inputs:  assert property (@(posedge Cin or posedge reset) !$isunknown({A,B,Cin,reset}));
  ap_no_x_outputs: assert property (@(posedge Cin or posedge reset) !$isunknown({Sum,Cout}));

  // Reset behavior
  ap_reset_clears: assert property (@(posedge reset) Sum == 4'h0);
  ap_reset_holds:  assert property (@(posedge Cin) reset |-> (Sum == 4'h0));

  // Functional correctness on Cin edge when not in reset
  ap_add_correct:  assert property (@(posedge Cin) !reset |-> {Cout, Sum} == (A + B + Cin));

  // Sum changes only on allowed events (immediate assertion)
  always @(Sum) assert ($rose(Cin) || $rose(reset))
    else $error("Sum changed without posedge Cin or posedge reset");

  // ----------------------------------
  // Coverage
  // ----------------------------------
  // Reset exercised
  cp_reset:        cover property (@(posedge reset) 1);

  // Both Cin polarities sampled
  cp_cin0:         cover property (@(posedge Cin) !reset && (Cin==1'b0));
  cp_cin1:         cover property (@(posedge Cin) !reset && (Cin==1'b1));

  // No-carry case
  cp_no_carry:     cover property (@(posedge Cin) !reset && (A + B + Cin) < 16 && (Cout == 1'b0));

  // Overflow (carry-out) case
  cp_overflow:     cover property (@(posedge Cin) !reset && (A + B + Cin) >= 16 && (Cout == 1'b1));

  // Full propagate chain example (all ones + Cin)
  cp_full_propag:  cover property (@(posedge Cin) !reset && A==4'hF && B==4'h0 && Cin==1'b1 && Cout==1'b1 && Sum==4'h0);

  // Carry-generate at LSB with no propagate (A0&B0)
  cp_lsb_generate: cover property (@(posedge Cin) !reset && A[0] && B[0] && (Cin==1'b0));

  // A mid-range mixed case
  cp_mid_mix:      cover property (@(posedge Cin) !reset && A==4'h5 && B==4'hA && Cin==1'b1);

endmodule

// Bind directive (place in a bind file or top-level)
// bind four_bit_adder four_bit_adder_sva sva (.*);