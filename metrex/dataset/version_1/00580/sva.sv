// SVA checker for seven_to_one
module seven_to_one_sva (
  input logic in0, in1, in2, in3, in4, in5, in6,
  input logic out,
  // bind to DUT internal nets for structural checks
  input logic or0_out, or1_out, or2_out, or3_out, or4_out, or5_out
);

  // Create a combinational sampling event for concurrent properties
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Convenience vector
  wire [6:0] iv = {in6,in5,in4,in3,in2,in1,in0};

  // X/Z checks
  assert property (!$isunknown(iv)) else $error("seven_to_one: inputs contain X/Z");
  assert property (!$isunknown(out)) else $error("seven_to_one: out is X/Z");

  // Functional equivalence (golden behavior)
  assert property (out == (|iv)) else $error("seven_to_one: out != OR of inputs");

  // Structural chain correctness
  assert property (or0_out == (in0 | in1))                      else $error("or0_out mismatch");
  assert property (or1_out == (in0 | in1 | in2))                else $error("or1_out mismatch");
  assert property (or2_out == (in0 | in1 | in2 | in3))          else $error("or2_out mismatch");
  assert property (or3_out == (in0 | in1 | in2 | in3 | in4))    else $error("or3_out mismatch");
  assert property (or4_out == (in0 | in1 | in2 | in3 | in4 | in5)) else $error("or4_out mismatch");
  assert property (or5_out == (|iv))                            else $error("or5_out mismatch");
  assert property (out == or5_out)                              else $error("buf/out mismatch");

  // Basic toggle correctness (no latency, no glitches under 0-delay model)
  assert property ($changed(iv) |-> out == (|iv)) else $error("out not updated with inputs");

  // Functional coverage
  // - All-zero case
  cover property (iv == 7'b0000000 && out == 1'b0);
  // - Single-hot cases (each input alone drives out)
  genvar i;
  generate
    for (i=0; i<7; i++) begin : gen_single_hot_cov
      cover property (iv == (7'b1 << i) && out == 1'b1);
    end
  endgenerate
  // - Multi-hot case (any two or more high)
  cover property ($countones(iv) >= 2 && out == 1'b1);
  // - Output edges
  cover property ($rose(out));
  cover property ($fell(out));

endmodule

// Bind into the DUT
bind seven_to_one seven_to_one_sva u_seven_to_one_sva (
  .in0(in0), .in1(in1), .in2(in2), .in3(in3), .in4(in4), .in5(in5), .in6(in6),
  .out(out),
  .or0_out(or0_out), .or1_out(or1_out), .or2_out(or2_out),
  .or3_out(or3_out), .or4_out(or4_out), .or5_out(or5_out)
);