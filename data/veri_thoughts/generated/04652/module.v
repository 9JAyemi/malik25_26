
module dual_edge_triggered_ff (
  input clk,
  input data,
  output reg q,
  output reg q_bar
);

reg [1:0] state;

always @(posedge clk) // fix the negative edge detection here
begin
  case (state)
    2'b00: begin
      q <= data;
      q_bar <= ~data;
      state <= 2'b01;
    end
    2'b01: begin
      q <= data;
      q_bar <= ~data;
      state <= 2'b10;
    end
    2'b10: begin
      q <= data;
      q_bar <= ~data;
      state <= 2'b11;
    end
    2'b11: begin
      q <= data;
      q_bar <= ~data;
      state <= 2'b00;
    end
    default: state <= 2'b00;
  endcase
end

endmodule