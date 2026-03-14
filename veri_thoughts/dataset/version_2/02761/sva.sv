module mux4to1_sva (
  input logic CLK,
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic out
);
  // No clock/reset in RTL; sampled on external CLK. Combinational mux behavior.

  // Out equals the bit selected by sel.
  check_mux_function: assert property (
    @(posedge CLK) (out === in[sel])
  );

  // When sel==00, out mirrors in[0].
  check_sel_00: assert property (
    @(posedge CLK) (sel == 2'b00) |-> (out === in[0])
  );

  // When sel==01, out mirrors in[1].
  check_sel_01: assert property (
    @(posedge CLK) (sel == 2'b01) |-> (out === in[1])
  );

  // When sel==10, out mirrors in[2].
  check_sel_10: assert property (
    @(posedge CLK) (sel == 2'b10) |-> (out === in[2])
  );

  // When sel==11, out mirrors in[3].
  check_sel_11: assert property (
    @(posedge CLK) (sel == 2'b11) |-> (out === in[3])
  );

  // If in and sel are stable, out must be stable.
  check_out_stable_when_inputs_stable: assert property (
    @(posedge CLK) ($stable(in) && $stable(sel)) |-> $stable(out)
  );

  // With sel stable, changing non-selected inputs does not change out.
  check_nonselected_inputs_do_not_affect_out: assert property (
    @(posedge CLK) ($stable(sel) && $changed(in) && !$changed(in[sel])) |-> $stable(out)
  );

  // With sel stable, changing the selected input changes out.
  check_out_follows_selected_input_change: assert property (
    @(posedge CLK) ($stable(sel) && $changed(in[sel])) |-> $changed(out)
  );

endmodule