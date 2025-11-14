// SVA for fifo. Bind this module to the DUT.
// Example: bind fifo fifo_sva #(.B(B),.W(W)) u_fifo_sva(.*);

module fifo_sva #(parameter int B=8, W=4)
(
  input  logic                 clk, reset,
  input  logic                 rd, wr,
  input  logic [B-1:0]         w_data,
  input  logic                 empty, full,
  input  logic [B-1:0]         r_data,
  // Internal DUT signals (connected by bind .*)
  input  logic                 wr_en,
  input  logic [W-1:0]         w_ptr_reg, w_ptr_next, w_ptr_succ,
  input  logic [W-1:0]         r_ptr_reg, r_ptr_next, r_ptr_succ,
  input  logic                 full_reg, empty_reg
);

  localparam int DEPTH = 1<<W;

  // Basic structural consistency
  assert property (@(posedge clk) full == full_reg);
  assert property (@(posedge clk) empty == empty_reg);
  assert property (@(posedge clk) !(full_reg && empty_reg));

  // Reset behavior
  assert property (@(posedge clk) reset |-> (w_ptr_reg==0 && r_ptr_reg==0 && empty_reg && !full_reg));

  // Flag-pointer relations (one-slot-empty FIFO)
  assert property (@(posedge clk) disable iff (reset) empty_reg == (w_ptr_reg==r_ptr_reg));
  assert property (@(posedge clk) disable iff (reset) full_reg  == (w_ptr_succ==r_ptr_reg));

  // Write enable equation
  assert property (@(posedge clk) wr_en == (wr && !full_reg));

  // Pointer next combinational correctness
  assert property (@(posedge clk) disable iff (reset)
                   (wr && !rd && !full_reg) |-> (w_ptr_next==w_ptr_succ && r_ptr_next==r_ptr_reg));
  assert property (@(posedge clk) disable iff (reset)
                   (rd && !wr && !empty_reg) |-> (r_ptr_next==r_ptr_succ && w_ptr_next==w_ptr_reg));
  assert property (@(posedge clk) disable iff (reset)
                   (rd && wr) |-> (w_ptr_next==w_ptr_succ && r_ptr_next==r_ptr_succ));

  // Sequential pointer updates (one cycle later)
  assert property (@(posedge clk) disable iff (reset)
                   (wr && !rd && !full_reg) |=> (w_ptr_reg==$past(w_ptr_reg)+1 && r_ptr_reg==$past(r_ptr_reg)));
  assert property (@(posedge clk) disable iff (reset)
                   (rd && !wr && !empty_reg) |=> (r_ptr_reg==$past(r_ptr_reg)+1 && w_ptr_reg==$past(w_ptr_reg)));
  assert property (@(posedge clk) disable iff (reset)
                   (wr && !rd &&  full_reg) |=> (w_ptr_reg==$past(w_ptr_reg)   && r_ptr_reg==$past(r_ptr_reg)));
  assert property (@(posedge clk) disable iff (reset)
                   (rd && !wr &&  empty_reg)|=> (r_ptr_reg==$past(r_ptr_reg)   && w_ptr_reg==$past(w_ptr_reg)));
  assert property (@(posedge clk) disable iff (reset)
                   (wr && rd) |=> (w_ptr_reg==$past(w_ptr_reg)+1 && r_ptr_reg==$past(r_ptr_reg)+1));

  // Flag updates after single ops
  assert property (@(posedge clk) disable iff (reset)
                   (wr && !rd && !full_reg) |=> (empty_reg==1'b0 &&
                                                 full_reg == (($past(w_ptr_reg)+1)==$past(r_ptr_reg))));
  assert property (@(posedge clk) disable iff (reset)
                   (rd && !wr && !empty_reg) |=> (full_reg==1'b0 &&
                                                  empty_reg == (($past(r_ptr_reg)+1)==$past(w_ptr_reg))));

  // Strong requirement for correct simultaneous full case: write must still occur (catches common bug)
  assert property (@(posedge clk) disable iff (reset) (wr && rd && full_reg) |-> wr_en);

  // Data integrity using a simple reference scoreboard on valid reads
  logic [B-1:0]     model_mem   [DEPTH];
  logic [DEPTH-1:0] model_valid;

  always_ff @(posedge clk) begin
    if (reset) begin
      model_valid <= '0;
    end else begin
      if (wr && !full_reg) begin
        model_mem[w_ptr_reg] <= w_data;
        model_valid[w_ptr_reg] <= 1'b1;
      end
      if (rd && !empty_reg) begin
        assert (model_valid[r_ptr_reg]) else $error("FIFO underflow/invalid read slot");
        assert (r_data == model_mem[r_ptr_reg]) else $error("FIFO data mismatch");
        model_valid[r_ptr_reg] <= 1'b0;
      end
    end
  end

  // Functional coverage
  cover property (@(posedge clk) disable iff (reset) wr && !full_reg);           // accept write
  cover property (@(posedge clk) disable iff (reset) rd && !empty_reg);          // accept read
  cover property (@(posedge clk) disable iff (reset) wr && rd);                  // simultaneous
  cover property (@(posedge clk) disable iff (reset) $rose(full_reg));           // become full
  cover property (@(posedge clk) disable iff (reset) $rose(empty_reg));          // become empty
  cover property (@(posedge clk) disable iff (reset)
                  (wr && !full_reg)[*1:$] ##1 full_reg);                         // writes lead to full
  cover property (@(posedge clk) disable iff (reset)
                  (rd && !empty_reg)[*1:$] ##1 empty_reg);                       // reads lead to empty
  cover property (@(posedge clk) disable iff (reset)
                  ($past(w_ptr_reg)=={W{1'b1}} && w_ptr_reg=={W{1'b0}}));        // w_ptr wrap
  cover property (@(posedge clk) disable iff (reset)
                  ($past(r_ptr_reg)=={W{1'b1}} && r_ptr_reg=={W{1'b0}}));        // r_ptr wrap
  cover property (@(posedge clk) disable iff (reset) (full_reg && wr && rd));    // both when full
  cover property (@(posedge clk) disable iff (reset) (empty_reg && wr && rd));   // both when empty

endmodule