module shift_register(input clk, input serial_in, output reg serial_out);
  reg [2:0] shift_reg;
  reg [1:0] mux_sel;
  wire d1, d2, d3;
  assign d1 = serial_in;
  assign d2 = shift_reg[0];
  assign d3 = shift_reg[1];
  
  always @(posedge clk) begin
    shift_reg <= {d3, d2, d1};
  end

  always @* begin
    case (mux_sel)
      2'b00: serial_out <= d1;
      2'b01: serial_out <= d2;
      2'b10: serial_out <= d3;
    endcase
  end

  initial begin
    mux_sel = 2'b10;
  end
endmodule