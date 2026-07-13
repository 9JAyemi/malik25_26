module zynq_reset(
  input slowest_sync_clk,
  input ext_reset_in,
  input aux_reset_in,
  input mb_debug_sys_rst,
  input dcm_locked,
  output mb_reset,
  output [0:0]bus_struct_reset,
  output [0:0]peripheral_reset,
  output [0:0]interconnect_aresetn,
  output [0:0]peripheral_aresetn
);

  // Reset mb_reset when mb_debug_sys_rst or ext_reset_in is asserted, or when dcm_locked is not asserted
  assign mb_reset = (mb_debug_sys_rst || ext_reset_in || !dcm_locked) ? 1'b1 : 1'b0;

  // Reset bus_struct_reset when ext_reset_in is asserted
  assign bus_struct_reset = ext_reset_in ? 1'b1 : 1'b0;

  // Reset peripheral_reset when aux_reset_in is asserted
  assign peripheral_reset = aux_reset_in ? 1'b1 : 1'b0;

  // Reset interconnect_aresetn when mb_reset is asserted
  assign interconnect_aresetn = mb_reset ? 1'b0 : 1'b1;

  // Reset peripheral_aresetn when either mb_reset or peripheral_reset is asserted
  assign peripheral_aresetn = (mb_reset || peripheral_reset) ? 1'b0 : 1'b1;

endmodule