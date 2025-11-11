// Bind these assertions into your fifo instance(s)
// Example: bind fifo fifo_sva f_sva();

module fifo_sva;
  // We are bound into fifo scope; internal signals are visible by name
  // Clocking and first-cycle guard (no reset in DUT)
  logic init_done;
  always_ff @(posedge clk) init_done <= 1'b1;
  default clocking cb @(posedge clk); endclocking
  default disable iff (!init_done)

  // -------------------------
  // Structural/basic checks
  // -------------------------
  // rd reflects not-empty (by design)
  assert property (rd == (rd_ptr != wr_ptr));

  // Pointers stay within 0..4 (DUT only uses 5 entries)
  assert property (wr_ptr < 3'd5);
  assert property (rd_ptr < 3'd5);

  // Pointers hold when not enabled
  assert property (!wr |=> wr_ptr == $past(wr_ptr));
  assert property (!rd |=> rd_ptr == $past(rd_ptr));

  // Pointer increment/wrap behavior
  assert property (wr && $past(wr_ptr) != 3'd4 |=> wr_ptr == $past(wr_ptr)+3'd1);
  assert property (wr && $past(wr_ptr) == 3'd4 |=> wr_ptr == 3'd0);

  assert property (rd && $past(rd_ptr) != 3'd4 |=> rd_ptr == $past(rd_ptr)+3'd1);
  assert property (rd && $past(rd_ptr) == 3'd4 |=> rd_ptr == 3'd0);

  // dout only updates on read, otherwise holds its value
  assert property (!rd |=> $stable(dout));

  // Memory write takes effect at next cycle at the addressed location
  // (write and read addresses are never equal when rd==1 by construction)
  assert property (wr |=> mem[$past(wr_ptr)] == $past(din));

  // No X-propagation on key outputs/state
  assert property (!$isunknown({rd, dout, wr_ptr, rd_ptr}));

  // -------------------------
  // Lightweight reference model (scoreboard) for functional checks
  // -------------------------
  logic [7:0] model_mem [0:4];
  logic [2:0] mwp, mrp;        // model pointers (0..4)
  int unsigned count;          // model occupancy (0..4)
  logic [7:0] exp_dout;

  // Initialize model
  initial begin
    mwp = '0; mrp = '0; count = 0; exp_dout = '0;
  end

  // Update model with same gating as DUT (rd is DUT output)
  always_ff @(posedge clk) begin
    // push
    if (wr) begin
      model_mem[mwp] <= din;
      mwp <= (mwp == 3'd4) ? 3'd0 : (mwp + 3'd1);
    end
    // pop
    if (rd) begin
      exp_dout <= model_mem[mrp];
      mrp <= (mrp == 3'd4) ? 3'd0 : (mrp + 3'd1);
    end
    // occupancy
    unique case ({wr,rd})
      2'b10: if (count < 5) count <= count + 1; // push only
      2'b01: if (count > 0) count <= count - 1; // pop only
      default: /* no change on 00 or 11 */;
    endcase
  end

  // Model vs DUT behavioral checks
  // Occupancy is bounded (no overflow/underflow)
  assert property (count >= 0 && count <= 4);

  // rd must reflect non-empty per model occupancy
  assert property (rd == (count != 0));

  // Read data must match model-popped data.
  // Check value assigned last cycle when rd was 1.
  assert property (rd |=> $past(dout) == $past(exp_dout));

  // Model/DUT pointer consistency (sanity)
  assert property (wr_ptr == mwp);
  assert property (rd_ptr == mrp);

  // -------------------------
  // Coverage
  // -------------------------
  // Pointer wrap on write and read
  cover property ($past(wr_ptr)==3'd4 && wr ##1 wr_ptr==3'd0);
  cover property ($past(rd_ptr)==3'd4 && rd ##1 rd_ptr==3'd0);

  // Fill to max then drain to empty
  cover property (count==0 ##1 (wr, count==1)[*4] ##1 (rd, count==0)[*4]);

  // Simultaneous write/read steady state
  cover property ((count!=0 && wr && rd)[*5]);

endmodule

// Bind directive (instantiate for each fifo)
// bind fifo fifo_sva f_sva();