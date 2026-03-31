
module FSM #(
  parameter n = 2,
  parameter m = 1
)(
  input [n-1:0] in,
  output reg [m-1:0] out,
  input clk,
  input rst
);

  parameter s = 4;

  parameter S0 = 2'b00;
  parameter S1 = 2'b01;
  parameter S2 = 2'b10;
  parameter S3 = 2'b11;

  parameter I0 = 2'b00;
  parameter I1 = 2'b01;
  parameter I2 = 2'b10;
  parameter I3 = 2'b11;

  parameter O0 = 1'b0;
  parameter O1 = 1'b1;

  reg [1:0] state;
  always @ (posedge clk, negedge rst) begin
    if (~rst) begin
      state <= S0;
      out <= O0;
    end else begin
      case (state)
        S0: begin
          if (in == I0) begin
            state <= S1;
            out <= O0;
          end else if (in == I1) begin
            state <= S2;
            out <= O1;
          end else begin
            state <= S0;
            out <= O0;
          end
        end
        S1: begin
          if (in == I0) begin
            state <= S2;
            out <= O0;
          end else if (in == I1) begin
            state <= S3;
            out <= O1;
          end else begin
            state <= S1;
            out <= O0;
          end
        end
        S2: begin
          if (in == I0) begin
            state <= S3;
            out <= O0;
          end else if (in == I1) begin
            state <= S0;
            out <= O1;
          end else begin
            state <= S2;
            out <= O0;
          end
        end
        S3: begin
          if (in == I0) begin
            state <= S0;
            out <= O0;
          end else if (in == I1) begin
            state <= S1;
            out <= O1;
          end else begin
            state <= S3;
            out <= O0;
          end
        end
      endcase
    end
  end

  initial begin
    state <= S0;
  end

  specify
    (in => out) = (10, 10);  // delay from in to out is 10 ns
  endspecify

endmodule