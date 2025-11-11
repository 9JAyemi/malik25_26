// SVA for data_storage. Bind this to the DUT.
// Focus: reset behavior, data capture/hold, valid mapping, data-output consistency, and coverage.

module data_storage_sva #(parameter int WIDTH = 32)
(
  input clk,
  input reset,
  input [WIDTH-1:0] in_data,
  input in_valid,
  input [WIDTH-1:0] out_data,
  input out_valid
);

  default clocking cb @(posedge clk); endclocking

  // Reset effects visible next cycle
  a_reset_clears_next: assert property (reset |=> (out_valid == 1'b0 && out_data == '0));

  // out_valid mirrors prior-cycle in_valid when not under reset
  a_out_valid_eq_past_in_valid: assert property (disable iff (reset)
    out_valid == $past(in_valid && !reset)
  );

  // On capture, out_data updates to prior-cycle in_data
  a_out_data_updates_on_valid: assert property (disable iff (reset)
    in_valid |=> (out_data == $past(in_data))
  );

  // Without capture, out_data holds value
  a_out_data_holds_without_valid: assert property (disable iff (reset)
    !in_valid |=> (out_data == $past(out_data))
  );

  // When out_valid is high, out_data must reflect the captured value
  a_out_valid_implies_out_data: assert property (disable iff (reset)
    out_valid |-> (out_data == $past(in_data))
  );

  // Outputs must be known when not in reset
  a_outputs_known: assert property (disable iff (reset)
    !$isunknown({out_valid, out_data})
  );

  // Coverage
  c_reset_seq:         cover property (reset ##1 !reset);
  c_single_capture:    cover property (disable iff (reset) in_valid);
  c_back_to_back_caps: cover property (disable iff (reset) in_valid ##1 in_valid);
  c_long_hold:         cover property (disable iff (reset) !in_valid [*3]);
  c_data_change_cap:   cover property (disable iff (reset) in_valid && $changed(in_data));
  c_out_changes:       cover property (disable iff (reset) $changed(out_data));

endmodule

bind data_storage data_storage_sva #(.WIDTH($bits(in_data))) i_data_storage_sva (.*);