
module processor_reset(
  input  input_sync_clk,
  input  ext_reset_in,
  input  aux_reset_in,
  input  mb_debug_sys_rst,
  input  dcm_locked,
  output reg mb_reset,
  output reg bus_struct_reset,
  output reg peripheral_reset,
  output reg interconnect_aresetn,
  output reg peripheral_aresetn
);

  parameter C_EXT_RST_WIDTH = 4;
  parameter C_AUX_RST_WIDTH = 4;
  parameter C_NUM_BUS_RST = 1;
  parameter C_NUM_INTERCONNECT_ARESETN = 1;
  parameter C_NUM_PERP_ARESETN = 1;
  parameter C_AUX_RESET_HIGH = 1'b0;
  parameter C_EXT_RESET_HIGH = 1'b1;
  parameter C_FAMILY = "artix7";

  reg [C_EXT_RST_WIDTH-1:0] ext_rst_count;
  reg [C_AUX_RST_WIDTH-1:0] aux_rst_count;
  reg [1:0] debug_rst_count;
  reg dcm_locked_1;
  
  always @(posedge input_sync_clk) begin
    ext_rst_count <= (ext_reset_in == C_EXT_RESET_HIGH) ? ext_rst_count + 1 : 0;
    aux_rst_count <= (aux_reset_in == C_AUX_RESET_HIGH) ? aux_rst_count + 1 : 0;
    debug_rst_count <= (mb_debug_sys_rst == 1'b1) ? debug_rst_count + 1 : 0;
    dcm_locked_1 <= dcm_locked;
  end

  always @(ext_rst_count or aux_rst_count or debug_rst_count) begin
    if (ext_rst_count == C_EXT_RST_WIDTH || aux_rst_count == C_AUX_RST_WIDTH || debug_rst_count == 2'd1) begin
      mb_reset <= 1'b1;
      bus_struct_reset <= 1'b1;
      peripheral_reset <= 1'b1;
    end

    else if (dcm_locked_1 == 1'b0) begin
      mb_reset <= 1'b0;
      bus_struct_reset <= 1'b0;
      peripheral_reset <= 1'b0;
    end
  end

  always @* begin
    interconnect_aresetn = (dcm_locked_1 == 1'b1) ? 1'b1 : 1'b0;
    peripheral_aresetn = (dcm_locked_1 == 1'b1) ? 1'b1 : 1'b0;
  end

endmodule