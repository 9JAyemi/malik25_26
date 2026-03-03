// SVA checker for zynq_reset
module zynq_reset_sva(
  input  logic               slowest_sync_clk,
  input  logic               ext_reset_in,
  input  logic               aux_reset_in,
  input  logic               mb_debug_sys_rst,
  input  logic               dcm_locked,
  input  logic               mb_reset,
  input  logic [0:0]         bus_struct_reset,
  input  logic [0:0]         peripheral_reset,
  input  logic [0:0]         interconnect_aresetn,
  input  logic [0:0]         peripheral_aresetn
);

  default clocking cb @ (posedge slowest_sync_clk); endclocking

  // Functional equivalence assertions (golden equations)
  assert property (mb_reset == (mb_debug_sys_rst || ext_reset_in || !dcm_locked));
  assert property (bus_struct_reset[0] == ext_reset_in);
  assert property (peripheral_reset[0] == aux_reset_in);
  assert property (interconnect_aresetn[0] == ~mb_reset);
  assert property (peripheral_aresetn[0] == ~(mb_reset || peripheral_reset[0]));

  // No-X on all outputs
  assert property (!$isunknown({mb_reset, bus_struct_reset[0], peripheral_reset[0],
                                interconnect_aresetn[0], peripheral_aresetn[0]}));

  // Cause -> effect (same-cycle) checks
  assert property (mb_debug_sys_rst |-> mb_reset);
  assert property (ext_reset_in     |-> mb_reset);
  assert property (!dcm_locked      |-> mb_reset);

  assert property (ext_reset_in     |-> bus_struct_reset[0]);
  assert property (aux_reset_in     |-> peripheral_reset[0]);

  assert property (mb_reset         |-> !interconnect_aresetn[0]);
  assert property (mb_reset || peripheral_reset[0] |-> !peripheral_aresetn[0]);

  // Effect cannot occur without at least one cause
  assert property (mb_reset |-> (mb_debug_sys_rst || ext_reset_in || !dcm_locked));
  assert property (bus_struct_reset[0] |-> ext_reset_in);
  assert property (peripheral_reset[0] |-> aux_reset_in);
  assert property (!interconnect_aresetn[0] |-> mb_reset);
  assert property (!peripheral_aresetn[0] |-> (mb_reset || peripheral_reset[0]));

  // Key scenario coverage (inputs and resultant outputs)
  cover property ( dcm_locked && !mb_debug_sys_rst && !ext_reset_in && !aux_reset_in
                   && !mb_reset && !bus_struct_reset[0] && !peripheral_reset[0]
                   && interconnect_aresetn[0] && peripheral_aresetn[0]);

  cover property ( dcm_locked &&  mb_debug_sys_rst && !ext_reset_in
                   && mb_reset &&  bus_struct_reset[0]==0 && peripheral_reset[0]==0
                   && !interconnect_aresetn[0] && !peripheral_aresetn[0]);

  cover property ( dcm_locked && !mb_debug_sys_rst &&  ext_reset_in
                   && mb_reset &&  bus_struct_reset[0] && peripheral_reset[0]==0
                   && !interconnect_aresetn[0] && !peripheral_aresetn[0]);

  cover property (!dcm_locked && !mb_debug_sys_rst && !ext_reset_in
                   && mb_reset &&  bus_struct_reset[0]==0 && peripheral_reset[0]==0
                   && !interconnect_aresetn[0] && !peripheral_aresetn[0]);

  cover property ( dcm_locked && !mb_debug_sys_rst && !ext_reset_in &&  aux_reset_in
                   && !mb_reset && !bus_struct_reset[0] &&  peripheral_reset[0]
                   && interconnect_aresetn[0] && !peripheral_aresetn[0]);

endmodule

// Bind into DUT
bind zynq_reset zynq_reset_sva sva_i (
  .slowest_sync_clk   (slowest_sync_clk),
  .ext_reset_in       (ext_reset_in),
  .aux_reset_in       (aux_reset_in),
  .mb_debug_sys_rst   (mb_debug_sys_rst),
  .dcm_locked         (dcm_locked),
  .mb_reset           (mb_reset),
  .bus_struct_reset   (bus_struct_reset),
  .peripheral_reset   (peripheral_reset),
  .interconnect_aresetn (interconnect_aresetn),
  .peripheral_aresetn (peripheral_aresetn)
);