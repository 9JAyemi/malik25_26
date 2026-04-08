module sequential_circuit (
  input clk,
  input a,
  input b,
  output [1:0] q
);

  reg [1:0] counter;
  reg flip_flop;

  always @(posedge clk) begin
    if (b) begin
      counter <= 2'b0;
    end else if (a) begin
      counter <= counter + 2'b1;
    end
  end

  always @(posedge clk) begin
    flip_flop <= counter[1];
  end

  assign q = counter;

endmodule
