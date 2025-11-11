// SVA checker for encodeBcd10to4
// Concise, functionally complete, and bind-ready
module encodeBcd10to4_sva (
  input logic                clk,
  input logic [0:8]          in,
  input logic [0:3]          out
);

  // Local spec (recompute DUT function compactly)
  logic nor0;
  assign nor0 = ~(~in[7] | ~in[8]); // = in[7] & in[8]

  logic out0_e, out1_e, out2_e, out3_e;
  assign out3_e = nor0;

  assign out2_e = ~( nor0 & ( (~in[3]) | (~in[4]) | (~in[5]) | (~in[6]) ) );

  assign out1_e = ~( nor0 & ( (~in[1] & in[3] & in[4])
                            | (~in[2] & in[3] & in[4])
                            | (~in[5])
                            | (~in[6]) ) );

  assign out0_e = ~( (~in[8])
                   | ( nor0 & ( (~in[0] & in[1] & in[3] & in[5])
                              | (~in[2] & in[3] & in[5])
                              | (~in[4] & in[5])
                              | (~in[6]) ) ) );

  default clocking @(posedge clk); endclocking
  default disable iff ($isunknown(in));

  // Equivalence checks (golden vs DUT)
  assert property (out[3] == out3_e);
  assert property (out[2] == out2_e);
  assert property (out[1] == out1_e);
  assert property (out[0] == out0_e);

  // Sanity: outputs known and combinational stability
  assert property (!$isunknown(out)) else $error("encodeBcd10to4: X/Z on out");
  assert property ($stable(in) |-> $stable(out));

  // Key implications (important path dominance)
  assert property (~in[8] |-> out[0] == 1'b0);                 // and4out term
  assert property ((nor0 && ~in[5]) |-> (out[1]==0 && out[2]==0)); // shared ~in5 term
  assert property ((nor0 && ~in[6]) |-> (out[1]==0 && out[2]==0)); // shared ~in6 term
  assert property ((nor0 && ~in[3]) |-> out[2]==0);
  assert property ((nor0 && ~in[4]) |-> out[2]==0);

  // Coverage: each output toggles, and each OR-path is exercised
  cover property ($rose(out[0]));  cover property ($fell(out[0]));
  cover property ($rose(out[1]));  cover property ($fell(out[1]));
  cover property ($rose(out[2]));  cover property ($fell(out[2]));
  cover property ($rose(out[3]));  cover property ($fell(out[3]));

  cover property (~in[8]);                         // and4out
  cover property (nor0 && ~in[6]);                 // and3/8/12 shared term
  cover property (nor0 && ~in[5]);                 // and7/11 shared term
  cover property (nor0 && ~in[3]);                 // and9
  cover property (nor0 && ~in[4]);                 // and10
  cover property (nor0 && ~in[0] && in[1] && in[3] && in[5]); // and0
  cover property (nor0 && ~in[2] && in[3] && in[5]);          // and1
  cover property (nor0 && ~in[4] && in[5]);                   // and2
  cover property (nor0 && ~in[1] && in[3] && in[4]);          // and5
  cover property (nor0 && ~in[2] && in[3] && in[4]);          // and6
endmodule

// Example bind (hook to your env clock)
// bind encodeBcd10to4 encodeBcd10to4_sva u_encodeBcd10to4_sva(.clk(tb_clk), .in(in), .out(out));