module mux_4to1_sva (
  input logic clk,
  input logic [3:0] data_in,
  input logic [1:0] sel,
  input logic [0:0] data_out
);

  // When sel==00, output equals data_in[0].
  check_sel_00_map: assert property (
    @(posedge clk) (sel == 2'b00) |-> (data_out == data_in[0])
  );

  // When sel==01, output equals data_in[1].
  check_sel_01_map: assert property (
    @(posedge clk) (sel == 2'b01) |-> (data_out == data_in[1])
  );

  // When sel==10, output equals data_in[2].
  check_sel_10_map: assert property (
    @(posedge clk) (sel == 2'b10) |-> (data_out == data_in[2])
  );

  // When sel==11, output equals data_in[3].
  check_sel_11_map: assert property (
    @(posedge clk) (sel == 2'b11) |-> (data_out == data_in[3])
  );

  // If sel is unknown (X/Z), default branch drives 0.
  check_default_on_unknown_sel: assert property (
    @(posedge clk) $isunknown(sel) |-> (data_out == 1'b0)
  );

  // Functional equivalence of mux select expression.
  check_functional_equivalence: assert property (
    @(posedge clk) data_out ==
      (sel[1] ? (sel[0] ? data_in[3] : data_in[2])
              : (sel[0] ? data_in[1] : data_in[0]))
  );

  // If sel and data_in are stable, data_out must remain stable (pure combinational).
  check_stable_when_inputs_stable: assert property (
    @(posedge clk) ($stable(sel) && $stable(data_in)) |-> $stable(data_out)
  );

  // Output changes only if sel changes or the selected input bit changes.
  check_output_change_has_cause: assert property (
    @(posedge clk) $changed(data_out) |-> ($changed(sel) || $changed(data_in[sel]))
  );

endmodule