module dynamic_gate_sva (
  input wire in,
  input wire clk,
  output reg out
);
  // Sequential logic: out is updated on the rising edge of clk based on the value of in
  sequential_logic: assert property (
    @(posedge clk) disable iff (!clk) out == (in ? 1'b1 : 1'b0)
  );
endmodule