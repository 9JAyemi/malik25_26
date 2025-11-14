// SVA for axi_protocol_converter_v2_1_b2s_incr_cmd
// Bindable, concise, checks key behavior and provides focused coverage.

module b2s_incr_cmd_sva #(
  parameter int C_AXI_ADDR_WIDTH = 32
)(
  input  logic                                 clk,
  input  logic                                 reset,
  input  logic [C_AXI_ADDR_WIDTH-1:0]          axaddr,
  input  logic [7:0]                           axlen,
  input  logic [2:0]                           axsize,
  input  logic                                 axhandshake,
  input  logic [C_AXI_ADDR_WIDTH-1:0]          cmd_byte_addr,
  input  logic                                 next,
  input  logic                                 next_pending,

  // internal signals
  input  logic                                 sel_first,
  input  logic [11:0]                          axaddr_incr,
  input  logic [8:0]                           axlen_cnt,
  input  logic                                 next_pending_r,
  input  logic [3:0]                           axsize_shift,
  input  logic [11:0]                          axsize_mask
);
  localparam int L_AXI_ADDR_LOW_BIT = (C_AXI_ADDR_WIDTH >= 12) ? 12 : 11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (cb !$isunknown({sel_first,next,axhandshake,axsize_shift,axsize_mask})); // no X on key controls

  // axsize_shift/mask correctness
  assert property (cb axsize_shift == (4'd1 << axsize[1:0]));
  assert property (cb (axsize_shift inside {4'd1,4'd2,4'd4,4'd8}));
  assert property (cb axsize_mask  == ~(axsize_shift - 1'b1));

  // cmd_byte_addr selection/mapping
  assert property (cb sel_first |-> (cmd_byte_addr == axaddr));
  generate
    if (C_AXI_ADDR_WIDTH > 12) begin : SVA_ADDR_GT_4K
      assert property (cb (!sel_first) |-> (cmd_byte_addr ==
        {axaddr[C_AXI_ADDR_WIDTH-1:L_AXI_ADDR_LOW_BIT], axaddr_incr[11:0]}));
    end else begin : SVA_ADDR_4K
      assert property (cb (!sel_first) |-> (cmd_byte_addr == axaddr_incr[11:0]));
    end
  endgenerate

  // axaddr_incr update rules
  assert property (cb ( sel_first && !next) |=> axaddr_incr == (axaddr[11:0] & axsize_mask));
  assert property (cb ( sel_first &&  next) |=> axaddr_incr == ((axaddr[11:0] & axsize_mask) + axsize_shift));
  assert property (cb (!sel_first &&  next) |=> axaddr_incr == ($past(axaddr_incr) + $past(axsize_shift)));
  assert property (cb (!sel_first && !next) |=> axaddr_incr == $past(axaddr_incr));

  // Alignment after any update (uses previous axsize_shift)
  assert property (cb ( sel_first)           |=> ((axaddr_incr & ($past(axsize_shift)-1)) == 0));
  assert property (cb (!sel_first && next)   |=> ((axaddr_incr & ($past(axsize_shift)-1)) == 0));

  // axlen_cnt / next_pending_r state machine
  assert property (cb (axhandshake) |=> (axlen_cnt == axlen));
  assert property (cb (axhandshake) |=> (next_pending_r == (axlen >= 1)));

  assert property (cb (!axhandshake && next && ($past(axlen_cnt) >  9'd1)) |=> (axlen_cnt == ($past(axlen_cnt)-1)));
  assert property (cb (!axhandshake && next && ($past(axlen_cnt) >  9'd1)) |=> (next_pending_r == ((($past(axlen_cnt)-1) >= 9'd1))));
  assert property (cb (!axhandshake && next && ($past(axlen_cnt) <= 9'd1)) |=> (axlen_cnt == 9'd0 && next_pending_r == 1'b0));

  assert property (cb (!axhandshake && !next) |=> (axlen_cnt == $past(axlen_cnt) && next_pending_r == $past(next_pending_r)));

  // Combinational next_pending mapping
  assert property (cb ( axhandshake) |-> (next_pending == (axlen >= 1)));
  assert property (cb (!axhandshake &&  next && (axlen_cnt >  9'd1)) |-> (next_pending == 1'b1));
  assert property (cb (!axhandshake &&  next && (axlen_cnt <= 9'd1)) |-> (next_pending == 1'b0));
  assert property (cb (!axhandshake && !next)                      |-> (next_pending == next_pending_r));

  // sel_first control
  assert property (cb (reset || axhandshake) |=> sel_first == 1'b1);
  assert property (cb (!reset && !axhandshake && next) |=> sel_first == 1'b0);
  assert property (cb (!reset && !axhandshake && !next) |=> sel_first == $past(sel_first));

  // Coverage: representative scenarios
  cover property (cb axhandshake ##1 sel_first && !next ##1 next); // first-beat then advance
  cover property (cb axhandshake && (axlen == 8'd0) ##1 !next_pending); // single-beat burst
  cover property (cb axhandshake && (axlen == 8'd1) ##1 next ##1 !next_pending); // 2-beat burst completes
  cover property (cb axhandshake && (axlen >= 8'd4) ##1 (!sel_first && next)[*4]); // multiple increments

  // Cover 4KB boundary crossing (only meaningful when address width > 12)
  generate if (C_AXI_ADDR_WIDTH > 12) begin
    cover property (cb (!sel_first && next &&
                        ($past(axaddr_incr[11:0]) + $past(axsize_shift) < $past(axaddr_incr[11:0]))));
  end endgenerate

endmodule

bind axi_protocol_converter_v2_1_b2s_incr_cmd
  b2s_incr_cmd_sva #(.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH))
  b2s_incr_cmd_sva_i (.*);