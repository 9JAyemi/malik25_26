// SVA binders for LUT1 and shift_register

// Assertions for LUT1 (pure combinational: O must equal I0)
module LUT1_sva (
  input logic I0,
  input logic O
);
  // Functional correctness
  always_comb assert (O === I0)
    else $error("LUT1: O must equal I0");

  // Coverage: exercise both polarities and edges
  cover property (@(posedge I0) O == 1'b1);
  cover property (@(negedge I0) O == 1'b0);
endmodule

bind LUT1 LUT1_sva u_lut1_sva (.I0(I0), .O(O));


// Assertions for shift_register
module shift_register_sva (
  input  logic [8:0] in,
  input  logic [8:0] out,
  input  logic       clk
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Core behavior: shift with serial input in[8]
  property p_shift;
    @(posedge clk) past_valid |-> out === { $past(out[7:0]), $past(in[8]) };
  endproperty
  assert property (p_shift)
    else $error("shift_register: shift behavior mismatch");

  // Known-propagation: when history is known, next state is known
  property p_known;
    @(posedge clk)
      past_valid && !$isunknown({$past(out), $past(in[8])})
      |-> !$isunknown(out);
  endproperty
  assert property (p_known)
    else $error("shift_register: X/Z propagated unexpectedly");

  // Coverage: a '1' injected on in[8] walks through all stages
  genvar i;
  generate
    for (i = 0; i < 9; i++) begin : cov_walk
      cover property (@(posedge clk) in[8] ##i out[i]);
    end
  endgenerate

  // Coverage: each output bit toggles both directions at least once
  generate
    for (i = 0; i < 9; i++) begin : cov_toggle
      cover property (@(posedge clk) $rose(out[i]));
      cover property (@(posedge clk) $fell(out[i]));
    end
  endgenerate
endmodule

bind shift_register shift_register_sva u_shift_register_sva (.in(in), .out(out), .clk(clk));