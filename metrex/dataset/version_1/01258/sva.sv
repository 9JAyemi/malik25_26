// SVA for the provided design. Bind these to top_module.

module top_module_sva (
  input               clk,
  input               reset,   // active-low
  input        [7:0]  in,
  input        [8:0]  parity_out,
  input               rise,
  input               down,
  input               active
);

  // Parity checker correctness (combinational mapping sampled on clk)
  assert property (@(posedge clk) parity_out[8] == ^in);
  assert property (@(posedge clk) parity_out[7:6] == 2'b00);     // zero-extend due to 6->8 bit assign
  assert property (@(posedge clk) parity_out[5:3] == in[6:4]);
  assert property (@(posedge clk) parity_out[2:0] == in[2:0]);

  // Edge detector behavior
  assert property (@(posedge clk) !reset |-> (!rise && !down));  // async reset forces outputs low
  assert property (@(posedge clk) !(rise && down));              // mutually exclusive

  // Edges correspond to input [0] transitions
  assert property (@(posedge clk) disable iff (!reset) rise == $rose(in[0]));
  assert property (@(posedge clk) disable iff (!reset) down == $fell(in[0]));
  assert property (@(posedge clk) disable iff (!reset) $stable(in[0]) |-> (!rise && !down));

  // Active signal function
  assert property (@(posedge clk)
    active == (((parity_out[8] == 1'b0) && rise) || ((parity_out[8] == 1'b1) && down))
  );

  // Coverage
  cover property (@(posedge clk) disable iff (!reset) (parity_out[8] == 1'b0) && $rose(in[0]) && active);
  cover property (@(posedge clk) disable iff (!reset) (parity_out[8] == 1'b1) && $fell(in[0]) && active);
  cover property (@(posedge clk) disable iff (!reset) (parity_out[8] == 1'b0) && $fell(in[0]) && !active);
  cover property (@(posedge clk) disable iff (!reset) (parity_out[8] == 1'b1) && $rose(in[0]) && !active);
  cover property (@(posedge clk) !reset ##1 reset ##1 $rose(in[0])); // reset recovery then a rise

endmodule

bind top_module top_module_sva sva_i (.*);