// SVA checker for fifo. Bind into the DUT.
// Focus: pointer/flag protocol, simultaneous ops, data integrity, wrap, and coverage.

module fifo_sva #(parameter int B=8, W=4)
(
  input  logic                 clk,
  input  logic                 reset,
  input  logic                 wr,
  input  logic                 rd,
  input  logic [B-1:0]         w_data,
  input  logic [B-1:0]         r_data,

  // Internal DUT signals (bound)
  input  logic [W-1:0]         w_ptr_reg,
  input  logic [W-1:0]         r_ptr_reg,
  input  logic [W-1:0]         w_ptr_succ,
  input  logic [W-1:0]         r_ptr_succ,
  input  logic                 full_reg,
  input  logic                 empty_reg,
  input  logic                 wr_en
);

  localparam int DEPTH = 1 << W;

  // Helpers
  logic wr_acc, rd_acc;
  always_comb begin
    wr_acc = wr && !full_reg;
    rd_acc = rd && !empty_reg;
  end

  // Golden occupancy model
  logic [W:0] occ;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) occ <= '0;
    else       occ <= occ + (wr_acc ? 1 : 0) - (rd_acc ? 1 : 0);
  end

  // Simple data scoreboard (mirrors writes accepted by DUT)
  logic [B-1:0] ref_mem [DEPTH-1:0];
  int i;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      for (i=0; i<DEPTH; i++) ref_mem[i] <= '0;
    end else if (wr_acc) begin
      ref_mem[w_ptr_reg] <= w_data;
    end
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset state must be sane (checked in clocked domain)
  assert property (reset |-> (w_ptr_reg==0 && r_ptr_reg==0 && empty_reg && !full_reg));

  // Basic protocol
  assert property (wr_en == (wr && !full_reg));
  assert property (!(full_reg && empty_reg));

  // Pointer updates must match accepted ops
  assert property (w_ptr_reg == $past(wr_acc ? w_ptr_succ : w_ptr_reg));
  assert property (r_ptr_reg == $past(rd_acc ? r_ptr_succ : r_ptr_reg));

  // Flags must reflect occupancy model
  assert property (occ inside {[0:DEPTH]});
  assert property (empty_reg == (occ==0));
  assert property (full_reg  == (occ==DEPTH));

  // Pointer/flag relationship
  assert property ((w_ptr_reg==r_ptr_reg) == (empty_reg || full_reg));
  assert property ((w_ptr_reg!=r_ptr_reg) |-> (!empty_reg && !full_reg));

  // No-op on disallowed ops
  assert property ((wr && full_reg)  |-> (w_ptr_reg == $past(w_ptr_reg) && full_reg == $past(full_reg) && empty_reg == $past(empty_reg)));
  assert property ((rd && empty_reg) |-> (r_ptr_reg == $past(r_ptr_reg) && full_reg == $past(full_reg) && empty_reg == $past(empty_reg)));

  // Simultaneous read+write when both are accepted: both pointers advance, flags unchanged
  assert property ((wr_acc && rd_acc) |-> (w_ptr_reg == $past(w_ptr_succ) &&
                                           r_ptr_reg == $past(r_ptr_succ) &&
                                           full_reg  == $past(full_reg)   &&
                                           empty_reg == $past(empty_reg)));

  // Data integrity on accepted reads
  assert property (rd_acc |-> r_data == $past(ref_mem[r_ptr_reg]));

  // Wrap-around coverage
  cover property (wr_acc && (w_ptr_reg==DEPTH-1) ##1 (w_ptr_reg==0));
  cover property (rd_acc && (r_ptr_reg==DEPTH-1) ##1 (r_ptr_reg==0));

  // Fill to full, then drain to empty
  cover property ((wr_acc)[*DEPTH] ##1 full_reg ##1 (rd_acc)[*DEPTH] ##1 empty_reg);

  // Simultaneous read+write in mid occupancy
  cover property (!empty_reg && !full_reg && wr_acc && rd_acc);

endmodule

// Bind into DUT
bind fifo fifo_sva #(.B(B), .W(W)) fifo_sva_i (
  .clk(clk),
  .reset(reset),
  .wr(wr),
  .rd(rd),
  .w_data(w_data),
  .r_data(r_data),
  .w_ptr_reg(w_ptr_reg),
  .r_ptr_reg(r_ptr_reg),
  .w_ptr_succ(w_ptr_succ),
  .r_ptr_succ(r_ptr_succ),
  .full_reg(full_reg),
  .empty_reg(empty_reg),
  .wr_en(wr_en)
);