module Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Edge_Detection_Router_Controller (
  // inputs:
  input [1:0] address,
  input chipselect,
  input clk,
  input reset_n,
  input write_n,
  input [31:0] writedata,

  // outputs:
  output out_port,
  output [31:0] readdata
);

  wire clk_en;
  reg data_out;
  wire out_port;
  wire read_mux_out;
  wire [31:0] readdata;

  assign clk_en = 1;

  //s1, which is an e_avalon_slave
  assign read_mux_out = {1 {(address == 0)}} & data_out;

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      data_out <= 0;
    end
    else if (chipselect && !write_n && (address == 0)) begin
      data_out <= writedata;
    end
  end

  assign readdata = {32'b0, read_mux_out};
  assign out_port = data_out;

endmodule