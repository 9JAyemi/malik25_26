
module soc_system_led_pio (
  input [1:0] address,
  input chipselect,
  input clk,
  input reset_n,
  input write_n,
  input [31:0] writedata,
  output reg [9:0] out_port,
  output [31:0] readdata
);

  wire clk_en;
  wire [9:0] read_mux_out;
  
  assign clk_en = 1;
  
  always @(posedge clk or negedge reset_n) begin
    if (~reset_n) begin
      out_port <= 10'b1111111111;
    end
    else if (chipselect && ~write_n && address == 2'b00) begin
      out_port <= writedata[9:0];
    end
  end
  
  assign read_mux_out = {10 {(address == 2'b00)}} & out_port;
  assign readdata = {22'b0, read_mux_out};
  
endmodule
