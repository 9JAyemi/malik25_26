module lfsr_counter(
  input clk, reset,
  output reg [SIZE-1:0] out
);

  parameter SIZE = 4;

  reg [SIZE-1:0] state;

  always @(posedge clk or posedge reset)
    begin
      if (reset) begin
        state <= 0;
        out <= 0;
      end
      else begin
        state <= {state[SIZE-2:0], state[SIZE-1] ^ state[SIZE-2] ^ 1'b1};
        out <= state;
      end
    end
endmodule