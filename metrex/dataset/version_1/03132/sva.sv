// SVA checker for mux4to1. Bind this to the DUT.
// Example bind:
// bind mux4to1 mux4to1_sva u_mux4to1_sva(.clk(tb_clk), .rst_n(tb_rst_n), .in(in), .sel(sel), .out(out));

module mux4to1_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  in,
  input logic [1:0]  sel,
  input logic        out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Disallow X/Z on select
  ap_sel_known:       assert property (!$isunknown(sel));

  // Functional equivalence when select is known
  ap_func_eq:         assert property (!$isunknown(sel) |-> (out === in[sel]));

  // If select and selected input are known, out must be known
  ap_no_x_on_out:     assert property (!$isunknown({sel, in[sel]}) |-> !$isunknown(out));

  // Mapping per select value (strong, 4-state)
  ap_map_00:          assert property ((sel == 2'b00) |-> (out === in[0]));
  ap_map_01:          assert property ((sel == 2'b01) |-> (out === in[1]));
  ap_map_10:          assert property ((sel == 2'b10) |-> (out === in[2]));
  ap_map_11:          assert property ((sel == 2'b11) |-> (out === in[3]));

  // Isolation: unselected inputs must not affect out
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : iso
      ap_iso: assert property ((sel != i && $changed(in[i])) |-> !$changed(out));
    end
  endgenerate

  // Coverage: see all selects and exercise each data path (input change propagates to out)
  cp_sel_00:          cover property (sel == 2'b00);
  cp_sel_01:          cover property (sel == 2'b01);
  cp_sel_10:          cover property (sel == 2'b10);
  cp_sel_11:          cover property (sel == 2'b11);

  generate
    for (i = 0; i < 4; i++) begin : cov_path
      cp_path_toggle: cover property (sel == i ##1 $changed(in[i]) ##1 $changed(out));
    end
  endgenerate

endmodule