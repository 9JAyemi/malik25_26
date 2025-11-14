// SVA for four_bit_adder
module four_bit_adder_sva
(
  input logic        Clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  Sum,
  input logic        Cout
);

  default clocking cb @(posedge Clk); endclocking

  // Functional correctness (5-bit sum)
  a_sum_ok: assert property ({Cout,Sum} == A + B + Cin);

  // X/Z sanitation on inputs and outputs at sampling
  a_no_x_inputs:  assert property (!$isunknown({A,B,Cin}));
  a_no_x_outputs: assert property (!$isunknown({Sum,Cout}));

  // Outputs are registered: no mid-cycle glitches (cheap check)
  a_no_glitch: assert property (@(negedge Clk) $stable({Sum,Cout}));

  // Key functional coverage
  c_no_carry:  cover property (((A+B+Cin) <= 4'hF) && (Cout == 1'b0));
  c_carry:     cover property (((A+B+Cin) >  4'hF) && (Cout == 1'b1));
  c_zero:      cover property (A==4'h0 && B==4'h0 && Cin==1'b0 &&
                               Sum==4'h0 && Cout==1'b0);
  c_full:      cover property (A==4'hF && B==4'hF && Cin==1'b1 &&
                               Sum==4'hF && Cout==1'b1);

  // Each sum bit toggles at least once
  genvar i;
  generate for (i=0; i<4; i++) begin : g_sum_toggles
    c_sum_bit_toggle: cover property ($changed(Sum[i]));
  end endgenerate

endmodule

// Bind to DUT
bind four_bit_adder four_bit_adder_sva sva_inst (
  .Clk(Clk), .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);