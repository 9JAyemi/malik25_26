// SVA for and_or_xnor_vector and its key behaviors.
// Bind into DUT. Concise, focuses on correctness and useful coverage.

module and_or_xnor_vector_sva
(
  input clk,
  input reset,
  input [3:0] in,
  input select,
  input out_and,
  input out_or,
  input out_xnor,
  input [2:0] outv
);

  // Expected 4-bit input to the gates based on select
  let exp_in = select ? {in[2], in[1], in[0], in[0]} : in;

  // Assert gate outputs match pure combinational functions of exp_in
  ap_and:  assert property (@(posedge clk) disable iff (reset)
                            !$isunknown({in,select}) |-> out_and  == (&exp_in))
           else $error("out_and mismatch");

  ap_or:   assert property (@(posedge clk) disable iff (reset)
                            !$isunknown({in,select}) |-> out_or   == (|exp_in))
           else $error("out_or mismatch");

  ap_xnor: assert property (@(posedge clk) disable iff (reset)
                            !$isunknown({in,select}) |-> out_xnor == ~(^exp_in))
           else $error("out_xnor mismatch");

  // outv is intended to mirror in[2:0] (per module comment)
  ap_outv_vec: assert property (@(posedge clk) disable iff (reset)
                                !$isunknown(in[2:0]) |-> outv == {in[2], in[1], in[0]})
               else $error("outv should equal {in[2],in[1],in[0]}");

  // If inputs are known, outputs must be known (no X/Z leakage)
  ap_no_x: assert property (@(posedge clk) disable iff (reset)
                            !$isunknown({in,select}) |-> !$isunknown({out_and,out_or,out_xnor,outv}))
           else $error("Unknowns on outputs with known inputs");

  // Minimal but meaningful coverage
  c_sel_rise: cover property (@(posedge clk) disable iff (reset) $rose(select));
  c_sel_fall: cover property (@(posedge clk) disable iff (reset) $fell(select));

  // Cover extreme input patterns as seen by the gates
  c_all_zero: cover property (@(posedge clk) disable iff (reset) (exp_in == 4'b0000));
  c_all_one:  cover property (@(posedge clk) disable iff (reset) (exp_in == 4'b1111));

  // Cover both parity classes at the gate input
  c_even_par: cover property (@(posedge clk) disable iff (reset) (~(^exp_in))); // even parity
  c_odd_par:  cover property (@(posedge clk) disable iff (reset)  (^(exp_in))); // odd parity

  // Ensure all 3-bit slices of in[2:0] are exercised (drives outv functional space)
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : C_IN3_COMBOS
      cover property (@(posedge clk) disable iff (reset) (in[2:0] == i[2:0]));
    end
  endgenerate

endmodule

bind and_or_xnor_vector and_or_xnor_vector_sva aoxv_sva (.*);