
module priority_encoder (
  input clk,
  input reset,
  input in0,
  input in1,
  input in2,
  input in3,
  output reg [1:0] out,
  output reg valid
);

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      out <= 2'b00;
      valid <= 1'b0;
    end else begin
      casez({in3, in2, in1, in0})
        4'b0001: out <= 2'b00;
        4'b0010: out <= 2'b01;
        4'b0100: out <= 2'b10;
        4'b1000: out <= 2'b11;
        default: out <= out;
      endcase
      if (in0 || in1 || in2 || in3) begin
        valid <= 1'b1;
      end else begin
        valid <= 1'b0;
      end
    end
  end

endmodule