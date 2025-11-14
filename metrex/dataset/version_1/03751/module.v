module shift_register (
  input clk,
  input load,
  input [3:0] data_in,
  output [3:0] data_out
);

  reg [3:0] shift_reg;

  always @(posedge clk) begin
    if (load) begin
      shift_reg <= data_in;
    end else begin
      shift_reg <= {shift_reg[2:0], shift_reg[3]};
    end
  end

  assign data_out = shift_reg;

endmodule
