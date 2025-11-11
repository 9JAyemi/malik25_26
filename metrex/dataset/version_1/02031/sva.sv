// SVA for processor_reset
// Quality-focused, concise checks + essential coverage

module processor_reset_sva #(
  parameter C_EXT_RST_WIDTH = 4,
  parameter C_AUX_RST_WIDTH = 4,
  parameter C_NUM_BUS_RST = 1,
  parameter C_NUM_INTERCONNECT_ARESETN = 1,
  parameter C_NUM_PERP_ARESETN = 1,
  parameter C_AUX_RESET_HIGH = 1'b0,
  parameter C_EXT_RESET_HIGH = 1'b1
)(
  input  logic                 input_sync_clk,
  input  logic                 ext_reset_in,
  input  logic                 aux_reset_in,
  input  logic                 mb_debug_sys_rst,
  input  logic                 dcm_locked,
  input  logic                 mb_reset,
  input  logic                 bus_struct_reset,
  input  logic                 peripheral_reset,
  input  logic                 interconnect_aresetn,
  input  logic                 peripheral_aresetn,
  input  logic [C_EXT_RST_WIDTH-1:0] ext_rst_count,
  input  logic [C_AUX_RST_WIDTH-1:0] aux_rst_count,
  input  logic [1:0]           debug_rst_count,
  input  logic                 dcm_locked_1
);

  default clocking cb @(posedge input_sync_clk); endclocking

  // Pipeline check for dcm_locked_1 (guarded against first-cycle X)
  assert property ( $past(1'b1) && !$isunknown({dcm_locked_1,$past(dcm_locked)}) |-> dcm_locked_1 == $past(dcm_locked) );

  // Counters increment when active, clear when inactive
  assert property ( (ext_reset_in == C_EXT_RESET_HIGH) |-> ext_rst_count == $past(ext_rst_count,1,'0) + 1 );
  assert property ( (ext_reset_in != C_EXT_RESET_HIGH) |-> ext_rst_count == '0 );

  assert property ( (aux_reset_in == C_AUX_RESET_HIGH) |-> aux_rst_count == $past(aux_rst_count,1,'0) + 1 );
  assert property ( (aux_reset_in != C_AUX_RESET_HIGH) |-> aux_rst_count == '0 );

  assert property ( (mb_debug_sys_rst == 1'b1) |-> debug_rst_count == $past(debug_rst_count,1,'0) + 1 );
  assert property ( (mb_debug_sys_rst != 1'b1) |-> debug_rst_count == '0 );

  // Output resets must assert when any threshold condition is met
  assert property ( (ext_rst_count == C_EXT_RST_WIDTH
                  || aux_rst_count == C_AUX_RST_WIDTH
                  || debug_rst_count == 2'd1)
                    |-> (mb_reset && bus_struct_reset && peripheral_reset) );

  // When no threshold, and dcm_locked_1 is low, outputs must be low
  assert property ( (dcm_locked_1 == 1'b0)
                    && !(ext_rst_count == C_EXT_RST_WIDTH
                      || aux_rst_count == C_AUX_RST_WIDTH
                      || debug_rst_count == 2'd1)
                    |-> (!mb_reset && !bus_struct_reset && !peripheral_reset) );

  // Active-low resets strictly follow dcm_locked_1
  assert property ( interconnect_aresetn == dcm_locked_1 );
  assert property ( peripheral_aresetn    == dcm_locked_1 );

  // Basic X-propagation guard after first cycle
  assert property ( $past(1'b1) |-> !$isunknown({mb_reset,bus_struct_reset,peripheral_reset,
                                                interconnect_aresetn,peripheral_aresetn,
                                                ext_rst_count,aux_rst_count,debug_rst_count,
                                                dcm_locked_1}) );

  // Coverage
  cover property ( (ext_reset_in == C_EXT_RESET_HIGH)[*C_EXT_RST_WIDTH]
                   ##0 (mb_reset && bus_struct_reset && peripheral_reset) );

  cover property ( (aux_reset_in == C_AUX_RESET_HIGH)[*C_AUX_RST_WIDTH]
                   ##0 (mb_reset && bus_struct_reset && peripheral_reset) );

  cover property ( mb_debug_sys_rst && (debug_rst_count == 2'd1)
                   && (mb_reset && bus_struct_reset && peripheral_reset) );

  cover property ( !dcm_locked_1 ##1 dcm_locked_1
                   && interconnect_aresetn && peripheral_aresetn );

  cover property ( dcm_locked_1 ##1 !dcm_locked_1
                   && !interconnect_aresetn && !peripheral_aresetn );

  // Cover deassert of outputs when unlocked and no threshold
  cover property ( (dcm_locked_1 == 1'b0)
                   && !(ext_rst_count == C_EXT_RST_WIDTH
                     || aux_rst_count == C_AUX_RST_WIDTH
                     || debug_rst_count == 2'd1)
                   && (!mb_reset && !bus_struct_reset && !peripheral_reset) );

endmodule

// Bind into DUT
bind processor_reset processor_reset_sva #(
  .C_EXT_RST_WIDTH(C_EXT_RST_WIDTH),
  .C_AUX_RST_WIDTH(C_AUX_RST_WIDTH),
  .C_NUM_BUS_RST(C_NUM_BUS_RST),
  .C_NUM_INTERCONNECT_ARESETN(C_NUM_INTERCONNECT_ARESETN),
  .C_NUM_PERP_ARESETN(C_NUM_PERP_ARESETN),
  .C_AUX_RESET_HIGH(C_AUX_RESET_HIGH),
  .C_EXT_RESET_HIGH(C_EXT_RESET_HIGH)
) processor_reset_sva_i (
  .input_sync_clk,
  .ext_reset_in,
  .aux_reset_in,
  .mb_debug_sys_rst,
  .dcm_locked,
  .mb_reset,
  .bus_struct_reset,
  .peripheral_reset,
  .interconnect_aresetn,
  .peripheral_aresetn,
  .ext_rst_count,
  .aux_rst_count,
  .debug_rst_count,
  .dcm_locked_1
);