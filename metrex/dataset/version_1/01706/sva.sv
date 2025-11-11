// SVA for register_monitor and lab9_soc_nios2_qsys_0_jtag_debug_module_wrapper
// Bind-only, concise, high-quality checks and minimal but meaningful coverage.

`ifndef REGISTER_MONITOR_SVA
`define REGISTER_MONITOR_SVA

module register_monitor_sva
(
  input wire        clk,
  input wire        reset_n,
  input wire [31:0] MonDReg,
  input wire        enable,
  input wire [31:0] monitored_value
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero
  ap_rm_reset_zero: assert property (cb !reset_n |-> monitored_value == 32'h0);

  // Update when enabled (1-cycle latency)
  ap_rm_update: assert property (cb disable iff (!reset_n)
                                 enable |=> monitored_value == $past(MonDReg));

  // Hold when not enabled
  ap_rm_hold:   assert property (cb disable iff (!reset_n)
                                 !enable |=> monitored_value == $past(monitored_value));

  // No X on key signals
  ap_rm_no_x:   assert property (cb !$isunknown({reset_n, enable, monitored_value}));

  // Coverage
  cp_rm_reset_pulse: cover property (cb $fell(reset_n) ##1 $rose(reset_n));
  cp_rm_update:      cover property (cb disable iff (!reset_n)
                                     enable && (MonDReg != $past(MonDReg))
                                     ##1 monitored_value == $past(MonDReg));
endmodule

bind register_monitor register_monitor_sva u_register_monitor_sva (.*);

`endif


`ifndef WRAPPER_SVA
`define WRAPPER_SVA

module lab9_soc_nios2_qsys_0_jtag_debug_module_wrapper_sva
(
  input  wire        clk,
  input  wire        reset_n,
  input  wire [31:0] MonDReg,

  input  wire [37:0] jdo,
  input  wire        jrst_n,
  input  wire        st_ready_test_idle,
  input  wire        take_action_break_a,
  input  wire        take_action_break_b,
  input  wire        take_action_break_c,
  input  wire        take_action_ocimem_a,
  input  wire        take_action_ocimem_b,
  input  wire        take_action_tracectrl,
  input  wire        take_action_tracemem_a,
  input  wire        take_action_tracemem_b,
  input  wire        take_no_action_break_a,
  input  wire        take_no_action_break_b,
  input  wire        take_no_action_break_c,
  input  wire        take_no_action_ocimem_a,
  input  wire        take_no_action_tracemem_a
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior on jdo lower 32
  ap_wr_reset_zero: assert property (cb !reset_n |-> jdo[31:0] == 32'h0);

  // Upper bits are constant zeros
  ap_wr_jdo_upper_zero: assert property (cb jdo[37:32] == 6'b0);

  // Constant outputs
  ap_wr_const_zeros: assert property (cb
    {jrst_n, st_ready_test_idle,
     take_action_break_a, take_action_break_b, take_action_break_c,
     take_action_ocimem_a, take_action_ocimem_b, take_action_tracectrl,
     take_action_tracemem_a, take_action_tracemem_b} == 10'b0);

  ap_wr_const_ones: assert property (cb
    {take_no_action_break_a, take_no_action_break_b, take_no_action_break_c,
     take_no_action_ocimem_a, take_no_action_tracemem_a} == 5'b1);

  // Data path: monitor enabled => jdo mirrors MonDReg with 1-cycle latency
  ap_wr_jdo_follows: assert property (cb disable iff (!reset_n)
                                      jdo[31:0] == $past(MonDReg));

  // No spurious jdo change when MonDReg is stable
  ap_wr_no_spurious: assert property (cb disable iff (!reset_n)
                                      $stable(MonDReg) |=> $stable(jdo[31:0]));

  // No X on outputs
  ap_wr_no_x_outs: assert property (cb
    !$isunknown({jdo, jrst_n, st_ready_test_idle,
                 take_action_break_a, take_action_break_b, take_action_break_c,
                 take_action_ocimem_a, take_action_ocimem_b, take_action_tracectrl,
                 take_action_tracemem_a, take_action_tracemem_b,
                 take_no_action_break_a, take_no_action_break_b, take_no_action_break_c,
                 take_no_action_ocimem_a, take_no_action_tracemem_a}));

  // Coverage
  cp_wr_reset_pulse: cover property (cb $fell(reset_n) ##1 $rose(reset_n));
  cp_wr_data_flow:   cover property (cb disable iff (!reset_n)
                                     MonDReg != $past(MonDReg)
                                     ##1 jdo[31:0] == $past(MonDReg));
  cp_wr_jdo_change:  cover property (cb disable iff (!reset_n)
                                     jdo[31:0] != $past(jdo[31:0]));
endmodule

bind lab9_soc_nios2_qsys_0_jtag_debug_module_wrapper
     lab9_soc_nios2_qsys_0_jtag_debug_module_wrapper_sva
     u_wrapper_sva (.*);

`endif