// SVA for decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_proc_sys_reset
module proc_sys_reset_sva (
  input  logic slowest_sync_clk,
  input  logic ext_reset_in,
  input  logic aux_reset_in,
  input  logic mb_debug_sys_rst,
  input  logic dcm_locked,
  input  logic mb_reset,
  input  logic [0:0] bus_struct_reset,
  input  logic [0:0] peripheral_reset,
  input  logic [0:0] interconnect_aresetn,
  input  logic [0:0] peripheral_aresetn
);
  default clocking cb @(posedge slowest_sync_clk); endclocking

  // Combinational outputs equivalence (guard unknowns)
  assert property (!$isunknown({ext_reset_in, mb_debug_sys_rst, bus_struct_reset})
                   |-> bus_struct_reset[0] == (ext_reset_in | mb_debug_sys_rst));
  assert property (!$isunknown({aux_reset_in, mb_debug_sys_rst, peripheral_reset})
                   |-> peripheral_reset[0] == (aux_reset_in | mb_debug_sys_rst));
  assert property (!$isunknown({mb_debug_sys_rst, interconnect_aresetn, peripheral_aresetn})
                   |-> (interconnect_aresetn[0] == ~mb_debug_sys_rst)
                    && (peripheral_aresetn[0]   == ~mb_debug_sys_rst));

  // mb_reset synchronous behavior
  assert property (dcm_locked &&  mb_debug_sys_rst |=> mb_reset == 1'b0);
  assert property (dcm_locked && !mb_debug_sys_rst |=> mb_reset == 1'b1);
  assert property (!dcm_locked |=> $stable(mb_reset));
  assert property (dcm_locked && $stable(mb_debug_sys_rst) |=> $stable(mb_reset));

  // Knownness when inputs known
  assert property (!$isunknown({ext_reset_in, aux_reset_in, mb_debug_sys_rst})
                   |-> !$isunknown({bus_struct_reset, peripheral_reset, interconnect_aresetn, peripheral_aresetn}));
  assert property (!$isunknown({dcm_locked, mb_debug_sys_rst}) |-> !$isunknown(mb_reset));

  // Targeted coverage
  cover property (dcm_locked &&  mb_debug_sys_rst |=> mb_reset == 1'b0);
  cover property (dcm_locked && !mb_debug_sys_rst |=> mb_reset == 1'b1);
  cover property (!dcm_locked ##1 !dcm_locked && $stable(mb_reset));
  cover property (!mb_debug_sys_rst ##1 $rose(ext_reset_in) && !mb_debug_sys_rst ##0 bus_struct_reset[0]);
  cover property (!mb_debug_sys_rst ##1 $rose(aux_reset_in)  && !mb_debug_sys_rst ##0 peripheral_reset[0]);
  cover property ($rose(mb_debug_sys_rst)
                  ##0 (bus_struct_reset[0] && peripheral_reset[0] && !interconnect_aresetn[0] && !peripheral_aresetn[0]));
endmodule

bind decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_proc_sys_reset proc_sys_reset_sva
  i_proc_sys_reset_sva (
    .slowest_sync_clk(slowest_sync_clk),
    .ext_reset_in(ext_reset_in),
    .aux_reset_in(aux_reset_in),
    .mb_debug_sys_rst(mb_debug_sys_rst),
    .dcm_locked(dcm_locked),
    .mb_reset(mb_reset),
    .bus_struct_reset(bus_struct_reset),
    .peripheral_reset(peripheral_reset),
    .interconnect_aresetn(interconnect_aresetn),
    .peripheral_aresetn(peripheral_aresetn)
  );