// SVA checker for mux_256to1
module mux_256to1_sva #(parameter int DATA_WIDTH = 3) (
  input logic                     clk,
  input logic                     rst_n,
  input logic [DATA_WIDTH*256-1:0] data_in,
  input logic [8:0]               sel,
  input logic [DATA_WIDTH-1:0]    out
);
  localparam int DW = DATA_WIDTH;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic well-formedness
  a_sel_known:    assert property (!$isunknown(sel));
  a_sel_in_range: assert property (sel < 256);

  // Functional equivalence (core check)
  a_mux_func: assert property (out == data_in[sel*DW +: DW]);

  // If selected slice is known, out must be known and equal
  a_no_x_on_known: assert property ((sel < 256) && !$isunknown(data_in[sel*DW +: DW])
                                    |-> (!$isunknown(out) && out == data_in[sel*DW +: DW]));

  // Independence: changes to unselected inputs must not affect out
  a_independence: assert property ($stable(sel) &&
                                   $changed(data_in) &&
                                   !$changed(data_in[sel*DW +: DW])
                                   |-> $stable(out));

  // Responsiveness: change in selected slice must reflect on out
  a_resp_selected_change: assert property ($stable(sel) &&
                                           $changed(data_in[sel*DW +: DW])
                                           |-> out == data_in[sel*DW +: DW]);

  // Coverage
  covergroup cg_sel @(posedge clk);
    coverpoint sel iff (rst_n && sel < 256) { bins all[] = {[0:255]}; }
  endgroup
  cg_sel sel_cg = new;

  c_lo: cover property (sel == 0);
  c_hi: cover property (sel == 255);
  c_change_through: cover property ($stable(sel) && $changed(data_in[sel*DW +: DW]) &&
                                    !$isunknown(data_in[sel*DW +: DW]) && rst_n);

endmodule

// Bind this checker to the DUT. Connect clk/rst_n from your environment.
bind mux_256to1 mux_256to1_sva #(.DATA_WIDTH(DATA_WIDTH))
  mux_256to1_sva_i (.clk(clk), .rst_n(rst_n), .data_in(data_in), .sel(sel), .out(out));