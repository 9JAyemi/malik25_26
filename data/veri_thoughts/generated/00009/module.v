module shift_reg(
  output [7:0] dout,
  input din,
  input clk,
  input en
);

  reg [7:0] shift_register = 8'h00;

  assign dout = shift_register;

  always @(posedge clk) begin
    if(en) begin
      shift_register[7:1] <= shift_register[6:0];
      shift_register[0] <= din;
    end
  end

endmodule