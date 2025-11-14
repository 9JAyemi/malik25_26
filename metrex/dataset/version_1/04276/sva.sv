// SVA for bitwise_or
`ifndef SYNTHESIS
module bitwise_or_sva (
  input clk,
  input reset,
  input  [31:0] input_bus_1,
  input  [31:0] input_bus_2,
  input  [31:0] output_bus
);
  default clocking cb @(posedge clk); endclocking

  // Reset forces zero on next cycle (sync reset)
  assert property (reset |=> output_bus == 32'h0);

  // Functional correctness (4-state aware) when not in reset
  assert property (!reset |=> (output_bus === (input_bus_1 | input_bus_2)));

  // If inputs are known, output must be known and correct
  assert property ((!reset && !$isunknown({input_bus_1, input_bus_2}))
                   |=> (!$isunknown(output_bus) && output_bus == (input_bus_1 | input_bus_2)));

  // Bit-level dominance sanity (concise, via generate)
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : g_or_bit
      assert property (!reset && (input_bus_1[i] === 1'b1) |=> (output_bus[i] === 1'b1));
      assert property (!reset && (input_bus_2[i] === 1'b1) |=> (output_bus[i] === 1'b1));
      assert property (!reset && (input_bus_1[i] === 1'b0) && (input_bus_2[i] === 1'b0) |=> (output_bus[i] === 1'b0));
    end
  endgenerate

  // Coverage
  cover property (reset ##1 !reset);                                    // reset pulse seen
  cover property (!reset && (input_bus_1|input_bus_2)==32'h0 ##1 output_bus==32'h0); // zero case
  cover property (!reset && (input_bus_1|input_bus_2)!=32'h0 ##1 output_bus!=32'h0); // non-zero case
endmodule

bind bitwise_or bitwise_or_sva u_bitwise_or_sva(
  .clk(clk),
  .reset(reset),
  .input_bus_1(input_bus_1),
  .input_bus_2(input_bus_2),
  .output_bus(output_bus)
);
`endif