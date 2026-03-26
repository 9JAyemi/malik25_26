module priority_encoder (
  input clk,
  input reset,
  input [3:0] in,
  input [3:0] valid,
  output reg [1:0] pos
);

  always @(posedge clk, negedge reset) begin
    if (!reset) begin
      pos <= 2'b0;
    end else begin
      if (valid[3]) begin
        pos <= 2'b11;
      end else if (valid[2]) begin
        pos <= 2'b10;
      end else if (valid[1]) begin
        pos <= 2'b01;
      end else if (valid[0]) begin
        pos <= 2'b00;
      end else begin
        pos <= 2'b0;
      end
    end
  end
  
endmodule
