// SVA for add_sub_pipeline + its adder instance (concise, high-signal-coverage)
bind add_sub_pipeline add_sub_pipeline_sva asrt(.clk(clk), .a(a), .b(b), .sub(sub), .sum(sum));

module add_sub_pipeline_sva (input logic clk,
                             input logic [31:0] a, b,
                             input logic        sub,
                             input logic [31:0] sum);

  localparam int W = 32;

  // past-valid gating (no reset provided)
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic sanity: no X on key control/output
  assert property (!$isunknown({sub, sum})));

  // Pipeline registers sample inputs each cycle
  assert property (a_reg == $past(a));
  assert property (b_reg == $past(b));

  // Transform and carry-in shape
  assert property (a_xor_b == (sub ? ~b : b));
  assert property (carry_in == {31'b0, sub});     // only bit0 used as Cin
  assert property (carry_in[W-1:1] == '0);

  // Combinational functional correctness (observed at posedge: uses a_reg(old)= $past(a), b(current), sub(current))
  assert property (sum == ($past(a) + (sub ? ~b : b) + sub));

  // Word-level correctness including final carry (adder output)
  assert property ({carry_out[W-1], sum} == (a_reg + a_xor_b + {31'b0, sub}));

  // Bit-level structural checks of the ripple adder
  // Stage 0
  assert property (adder_pipeline_inst.sum[0] ==
                   ((adder_pipeline_inst.a[0] ^ adder_pipeline_inst.b[0]) ^ adder_pipeline_inst.carry_in[0]));
  assert property (adder_pipeline_inst.carry_out[0] ==
                   ((adder_pipeline_inst.a[0] & adder_pipeline_inst.b[0]) |
                    ((adder_pipeline_inst.a[0] ^ adder_pipeline_inst.b[0]) & adder_pipeline_inst.carry_in[0])));

  // Stages 1..W-1
  genvar i;
  generate
    for (i = 1; i < W; i++) begin : gen_sva_ripple
      assert property (adder_pipeline_inst.sum[i] ==
                       ((adder_pipeline_inst.a[i] ^ adder_pipeline_inst.b[i]) ^ adder_pipeline_inst.carry_out[i-1]));
      assert property (adder_pipeline_inst.carry_out[i] ==
                       ((adder_pipeline_inst.a[i] & adder_pipeline_inst.b[i]) |
                        ((adder_pipeline_inst.a[i] ^ adder_pipeline_inst.b[i]) & adder_pipeline_inst.carry_out[i-1])));
    end
  endgenerate

  // Mode-specific shorthand checks
  assert property (sub == 1'b0 |-> sum == (a_reg + b));
  assert property (sub == 1'b1 |-> sum == (a_reg - b));

  // Functional coverage
  cover property (sub == 1'b0);
  cover property (sub == 1'b1);
  cover property ($rose(sub));
  cover property ($fell(sub));

  // Overflow/borrow edge cases
  cover property (a_reg == 32'hFFFF_FFFF && b == 32'd1 && sub == 1'b0 && carry_out[31] == 1'b1);
  cover property (a_reg == 32'h0000_0000 && b == 32'd1 && sub == 1'b1 && sum == 32'hFFFF_FFFF);
  cover property (a_reg == 32'hAAAA_AAAA && b == 32'h5555_5555 && sub == 1'b0 && sum == 32'hFFFF_FFFF);
  cover property (a_reg == 32'h0000_0000 && b == 32'h0000_0000 && sub == 1'b0 && sum == 32'h0000_0000);

endmodule