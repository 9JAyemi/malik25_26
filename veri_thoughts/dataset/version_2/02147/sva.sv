module processor_system_reset_sva (
  input logic slowest_sync_clk,
  input logic ext_reset_in,
  input logic aux_reset_in,
  input logic mb_debug_sys_rst,
  input logic dcm_locked,
  input logic mb_reset,
  input logic [0:0] bus_struct_reset,
  input logic [0:0] peripheral_reset,
  input logic [0:0] interconnect_aresetn,
  input logic [0:0] peripheral_aresetn
);

  ///// Functional mapping to reset request (sampled one cycle earlier) /////
  // All reset outputs equal the OR of {ext_reset_in, aux_reset_in, mb_debug_sys_rst, !dcm_locked} from the previous cycle.
  check_outputs_follow_reset_req: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      {mb_reset, bus_struct_reset[0], peripheral_reset[0], interconnect_aresetn[0], peripheral_aresetn[0]}
        == {5{ $past( ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked ) }}
  );

  ///// Explicit 1/0 drive under reset/non-reset conditions /////
  // If any reset cause was asserted or dcm_locked was LOW in the previous cycle, all outputs must be 1.
  check_outputs_one_when_reset_req: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $past( ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked )
        |-> (mb_reset && bus_struct_reset[0] && peripheral_reset[0] && interconnect_aresetn[0] && peripheral_aresetn[0])
  );

  // If no reset cause was asserted and dcm_locked was HIGH in the previous cycle, all outputs must be 0.
  check_outputs_zero_when_no_reset_req: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      !$past( ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked )
        |-> (!mb_reset && !bus_struct_reset[0] && !peripheral_reset[0] && !interconnect_aresetn[0] && !peripheral_aresetn[0])
  );

  ///// Consistency across reset outputs /////
  // All reset outputs are identical each cycle.
  check_all_outputs_equal: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      (mb_reset == bus_struct_reset[0]) &&
      (mb_reset == peripheral_reset[0]) &&
      (mb_reset == interconnect_aresetn[0]) &&
      (mb_reset == peripheral_aresetn[0])
  );

  ///// Edge relationships among outputs /////
  // All reset outputs rise in the same cycle.
  check_outputs_rise_together: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $rose(mb_reset) |-> $rose(bus_struct_reset[0]) && $rose(peripheral_reset[0]) && $rose(interconnect_aresetn[0]) && $rose(peripheral_aresetn[0])
  );

  // All reset outputs fall in the same cycle.
  check_outputs_fall_together: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $fell(mb_reset) |-> $fell(bus_struct_reset[0]) && $fell(peripheral_reset[0]) && $fell(interconnect_aresetn[0]) && $fell(peripheral_aresetn[0])
  );

  ///// Output edges follow reset request edges with one-cycle latency /////
  // A rising reset request causes all reset outputs to rise on the next cycle.
  check_reset_req_rise_causes_output_rise: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $rose( ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked )
        |=> $rose(mb_reset) && $rose(bus_struct_reset[0]) && $rose(peripheral_reset[0]) && $rose(interconnect_aresetn[0]) && $rose(peripheral_aresetn[0])
  );

  // A falling reset request causes all reset outputs to fall on the next cycle.
  check_reset_req_fall_causes_output_fall: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $fell( ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked )
        |=> $fell(mb_reset) && $fell(bus_struct_reset[0]) && $fell(peripheral_reset[0]) && $fell(interconnect_aresetn[0]) && $fell(peripheral_aresetn[0])
  );

  ///// Temporal stability /////
  // If all inputs are stable over a cycle, all outputs remain stable in the following cycle.
  check_stable_inputs_imply_stable_outputs: assert property (
    @(posedge slowest_sync_clk) disable iff ($initstate)
      $stable(ext_reset_in) && $stable(aux_reset_in) && $stable(mb_debug_sys_rst) && $stable(dcm_locked)
        |=> $stable({mb_reset, bus_struct_reset[0], peripheral_reset[0], interconnect_aresetn[0], peripheral_aresetn[0]})
  );

endmodule