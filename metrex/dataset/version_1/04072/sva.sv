// SVA for clock_multiplexer
module clock_multiplexer_sva #(parameter int n = 4)
(
  input  logic [3:0] clk,
  input  logic [1:0] control,
  input  logic       clk_out
);

  // Control must be in range whenever it changes
  assert_control_in_range: assert property (
    @(posedge control[0] or negedge control[0] or posedge control[1] or negedge control[1])
      !$isunknown(control) |-> (control < n)
  );

  // Output never falls (once set to 1, it stays 1)
  assert_no_fall: assert property (
    @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
      disable iff ($isunknown(clk_out))
      !$fell(clk_out)
  );

  // Any output change must coincide with a posedge of the selected clock
  assert_out_change_only_on_selected_edge: assert property (
    @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
      disable iff ($isunknown({control, clk_out}))
      $changed(clk_out) |-> $rose(clk[control])
  );

  genvar i;
  generate for (i = 0; i < n; i++) begin : GEN_SRC

    // Unselected clock posedge must not change output
    a_stable_when_not_selected: assert property (
      @(posedge clk[i])
        disable iff ($isunknown({control, clk[i], clk_out}))
        (control != i) |-> $stable(clk_out)
    );

    // When selected, by the next posedge of that source, output must be 1
    a_sets_high_when_selected: assert property (
      @(posedge clk[i])
        disable iff ($isunknown({control, clk[i], clk_out}))
        (control == i) |=> (clk_out == 1'b1)
    );

    // Coverage: see at least one posedge while selected
    c_selected_edge_seen: cover property (
      @(posedge clk[i]) (! $isunknown(control)) && (control == i)
    );

  end endgenerate

  // Coverage: control changes
  c_control_change: cover property (
    @(posedge control[0] or negedge control[0] or posedge control[1] or negedge control[1])
      $changed(control)
  );

endmodule

bind clock_multiplexer clock_multiplexer_sva #(.n(n)) clock_multiplexer_sva_b (.*);