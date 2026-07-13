module johnson_counter_sva (
  input logic clk,
  input logic reset,
  output logic [2:0] out
);

  reg [2:0] q;

  always @(posedge clk) begin
    if (reset) begin
      q <= 3'b000;
    end else begin
      q <= {q[1:0], q[2]};
    end
  end

  assign out = q;

  // At reset, the counter output must be 000
  reset_output: assert property (
    @(posedge clk) disable iff (!reset) (reset |-> out == 3'b000)
  );

  // The counter output must cycle through 000, 001, 010, 011, 100, 101, 110, 111
  counter_cycle: assert property (
    @(posedge clk) disable iff (!reset) (out inside {[3'b000:3'b111]})
  );

  // The counter output must not be stuck at any value
  counter_stuck: assert property (
    @(posedge clk) disable iff (!reset) (out !== out)
  );

endmodule