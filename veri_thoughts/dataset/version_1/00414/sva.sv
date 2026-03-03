// SVA checker for decoder_4to16
module decoder_4to16_sva #(
  parameter bit HAS_RST = 0
)(
  input  logic              clk,
  input  logic              rst_n,     // ignored if HAS_RST==0
  input  logic [3:0]        sel,
  input  logic [15:0]       out,
  input  logic [255:0]      in
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (HAS_RST ? !rst_n : 1'b0)

  // Sanity: no X/Z on controls or outputs
  ap_no_x_sel_out: assert property (!$isunknown(sel) && !$isunknown(out));

  // Functional equivalence: exact 4->16 decode
  ap_func:           assert property (out == (16'h1 << sel));

  // One-hot (exactly one bit set)
  ap_onehot:         assert property ($onehot(out));

  // Output independent of unused 'in'
  ap_in_indep:       assert property ($changed(in) && $stable(sel) |-> $stable(out));

  // If sel is stable, out must be stable
  ap_stable:         assert property ($stable(sel) |-> $stable(out));

  // Per-code coverage (also ensures mapping observed for all 16 values)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : GEN_CVG
      cp_sel_i: cover property ((sel == i) && (out == (16'h1 << i)));
    end
  endgenerate

  // Cover independence scenario exercised
  cp_in_indep: cover property ($changed(in) && $stable(sel) && $stable(out));

endmodule

// Example bind (edit clk/rst connections as appropriate to your environment):
// bind decoder_4to16 decoder_4to16_sva u_dec_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .sel(sel), .out(out), .in(in) );