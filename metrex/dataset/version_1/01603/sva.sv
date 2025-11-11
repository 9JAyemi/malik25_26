// SVA for Change2Negedge
// Checks: async reset drives zeros; 1-cycle negedge pipeline; no X on key signals.
// Includes focused coverage.

module Change2Negedge_sva #(parameter W=24) (
  input  logic                hsync_in,
  input  logic                vsync_in,
  input  logic                blnk_in,
  input  logic [W-1:0]        rgb_in,
  input  logic                clk,
  input  logic                rst,
  input  logic                hsync_out,
  input  logic                vsync_out,
  input  logic                blnk_out,
  input  logic [W-1:0]        rgb_out
);
  localparam int OUTW = W+3;
  wire [OUTW-1:0] ins  = {hsync_in,  vsync_in,  blnk_in,  rgb_in};
  wire [OUTW-1:0] outs = {hsync_out, vsync_out, blnk_out, rgb_out};

  default clocking cb @ (negedge clk); endclocking

  // Basic knowns
  a_rst_known:       assert property (cb !$isunknown(rst));
  a_outs_known:      assert property (cb !$isunknown(outs));
  a_ins_known_when_active: assert property (cb disable iff (rst) !$isunknown(ins));

  // Reset behavior: outputs are zero and stable while rst is asserted
  a_reset_zero:      assert property (cb rst |-> (outs == '0));
  a_reset_stable:    assert property (cb rst && $past(rst) |-> $stable(outs));

  // 1-cycle negedge pipeline when not in reset
  a_follow_1cycle:   assert property (cb disable iff (rst) outs == $past(ins));

  // Simple functional coverage
  c_reset_cycle:     cover  property (cb rst ##1 !rst);
  c_in_to_out:       cover  property (cb !rst && $changed(ins) ##1 outs == $past(ins));
  c_rgb_nonzero:     cover  property (cb !rst && (rgb_in != '0) ##1 (rgb_out == $past(rgb_in)));

endmodule

// Bind into all Change2Negedge instances
bind Change2Negedge Change2Negedge_sva #(.W(24)) Change2Negedge_sva_i (.*);