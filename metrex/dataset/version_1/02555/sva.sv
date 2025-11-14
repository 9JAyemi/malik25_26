// SVA for mig_7series_v4_0_axi_mc_simple_fifo
// Concise, high-value control/flag checks and coverage.
// Bind this checker to the DUT; no TB code required.

`ifndef SYNTHESIS
module mig_7series_v4_0_axi_mc_simple_fifo_sva #(
  parameter int C_WIDTH  = 8,
  parameter int C_AWIDTH = 4,
  parameter int C_DEPTH  = 16
)(
  input  logic                      clk,
  input  logic                      rst,
  input  logic                      wr_en,
  input  logic                      rd_en,
  input  logic [C_WIDTH-1:0]        din,
  input  logic [C_WIDTH-1:0]        dout,
  input  logic                      a_full,
  input  logic                      full,
  input  logic                      a_empty,
  input  logic                      empty,
  input  logic [C_AWIDTH-1:0]       cnt_read
);

  // Recompute DUT localparams
  localparam logic [C_AWIDTH-1:0] C_EMPTY     = {C_AWIDTH{1'b1}};
  localparam logic [C_AWIDTH-1:0] C_EMPTY_PRE = {C_AWIDTH{1'b0}};
  localparam logic [C_AWIDTH-1:0] C_FULL      = C_EMPTY - 1;
  localparam logic [C_AWIDTH-1:0] C_FULL_PRE  = (C_DEPTH < 8) ? (C_FULL-1) : (C_FULL-(C_DEPTH/8));
  localparam int DEP_M1 = (C_DEPTH>0)?(C_DEPTH-1):0;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Static/param sanity (compile-time)
  initial begin
    if (C_DEPTH != (1<<C_AWIDTH)) $error("FIFO param check failed: C_DEPTH(%0d) != 2**C_AWIDTH(%0d)", C_DEPTH, (1<<C_AWIDTH));
  end

  // Flag correctness (against cnt_read)
  assert property (full  == (cnt_read == C_FULL));
  assert property (empty == (cnt_read == C_EMPTY));
  assert property (a_full  == ((cnt_read >= C_FULL_PRE) && (cnt_read != C_EMPTY)));
  assert property (a_empty == (cnt_read == C_EMPTY_PRE));

  // Flag relationships
  assert property (!(full && empty));
  assert property (full |-> a_full);
  assert property (a_full |-> !empty);

  // Counter update rules
  assert property (wr_en && !rd_en |-> cnt_read == $past(cnt_read) + 1);
  assert property (!wr_en && rd_en |-> cnt_read == $past(cnt_read) - 1);
  assert property ((wr_en == rd_en) |-> $stable(cnt_read));

  // Protocol safety (no overflow/underflow)
  assert property (wr_en && !rd_en |-> !full);
  assert property (rd_en && !wr_en |-> !empty);

  // Idle stability
  assert property (!wr_en && !rd_en |-> $stable(dout));

  // Coverage: reach and traverse interesting states
  cover property (!full  ##[1:$] full);
  cover property (!empty ##[1:$] empty);
  cover property (empty ##1 (wr_en && !rd_en)[*DEP_M1] ##1 full);
  cover property (full  ##1 (!wr_en && rd_en)[*DEP_M1] ##1 empty);
  cover property (empty ##1 (wr_en && !rd_en)[*DEP_M1] ##1 full ##1 (!wr_en && rd_en)[*DEP_M1] ##1 empty);
  cover property (wr_en && rd_en); // simultaneous read+write
  cover property (a_full);
  cover property (a_empty);
  cover property ((cnt_read==C_FULL_PRE)  && wr_en && !rd_en ##1 full);
  cover property ((cnt_read==C_EMPTY_PRE) && !wr_en && rd_en ##1 a_empty);

endmodule

// Bind into the DUT
bind mig_7series_v4_0_axi_mc_simple_fifo
  mig_7series_v4_0_axi_mc_simple_fifo_sva #(
    .C_WIDTH (C_WIDTH),
    .C_AWIDTH(C_AWIDTH),
    .C_DEPTH (C_DEPTH)
  ) fifo_sva_i (
    .clk     (clk),
    .rst     (rst),
    .wr_en   (wr_en),
    .rd_en   (rd_en),
    .din     (din),
    .dout    (dout),
    .a_full  (a_full),
    .full    (full),
    .a_empty (a_empty),
    .empty   (empty),
    .cnt_read(cnt_read)
  );
`endif