module nios_system_switches (
  input [1:0] address,
  input clk,
  input [7:0] in_port,
  input reset_n,
  output reg [31:0] readdata
);

  wire [7:0] data_in;
  wire [7:0] read_mux_out;
  wire clk_en;

  assign data_in = in_port;

  assign read_mux_out = {8 {(address == 2'b00)}} & data_in | 
                       {8 {(address == 2'b01)}} & {1'b0, data_in[7:1]} | 
                       {8 {(address == 2'b10)}} & {2'b00, data_in[7:2]} | 
                       {8 {(address == 2'b11)}} & data_in;

  assign clk_en = 1;

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      readdata <= 0;
    end else if (clk_en) begin
      readdata <= {32'b0, read_mux_out};
    end
  end

endmodule