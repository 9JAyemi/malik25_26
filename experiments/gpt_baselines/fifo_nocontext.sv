// black_box_sva.sv
// Assertion module for black_box FIFO
module black_box_sva #(
  parameter int depth = 8,
  parameter int width = 8,
  // Set these to 0 to weaken flag equivalence if you purposefully explore buggy variants
  parameter bit STRICT_FULL  = 1,
  parameter bit STRICT_EMPTY = 1
)(
  input logic clk,
  input logic rst_,
  // Mirror DUT interface
  input logic write_en,
  input logic read_en,
  input logic full_flag,
  input logic empty_flag,
  input logic [width-1:0] data_in,
  input logic [width-1:0] data_out,
  // Expose internals via bind (wr_ptr, rd_ptr, count, mem)
  input logic [3:0] wr_ptr,
  input logic [3:0] rd_ptr,
  input logic [3:0] count
);

  // ------------------------------------------------------------
  // Helper derived handshake intent
  // ------------------------------------------------------------
  logic eff_write, eff_read;

  always_comb begin
    // Reconstruct which branch should have actually performed a write/read
    // according to intended spec (not necessarily current buggy variant).
    eff_write = 1'b0;
    eff_read  = 1'b0;

    unique case ({write_en, read_en})
      2'b10: eff_write = (count < depth);          // write only
      2'b01: eff_read  = (count > 0);              // read only
      2'b11: begin
        if (count == 0)        eff_write = 1;      // empty -> write only
        else if (count == depth) eff_read = 1;     // full  -> read only
        else begin
          eff_write = 1; eff_read = 1;             // middle occupancy -> both
        end
      end
      default: ; // idle
    endcase
  end

  // ------------------------------------------------------------
  // 1. Reset state assertions
  // ------------------------------------------------------------
  // After reset assertion (first cycle after rst_ rises)
  property reset_state_p;
    @(posedge clk)
      (!rst_ && $rose(rst_)) |-> (count == 0 && wr_ptr == 0 && rd_ptr == 0);
  endproperty
  assert property (reset_state_p)
    else $error("RESET_STATE: count / pointers not zero after reset release");

  // ------------------------------------------------------------
  // 2. Count bounds
  // ------------------------------------------------------------
  assert property (@(posedge clk) disable iff (!rst_) count <= depth)
    else $error("COUNT_BOUNDS: count exceeded depth");

  assert property (@(posedge clk) disable iff (!rst_) count >= 0)
    else $error("COUNT_BOUNDS: count negative (should be impossible with unsigned)");

  // ------------------------------------------------------------
  // 3. Flag consistency (strict versions)
  // ------------------------------------------------------------
  if (STRICT_EMPTY) begin
    assert property (@(posedge clk) disable iff (!rst_) (empty_flag -> (count == 0)))
      else $error("EMPTY_FLAG: empty_flag high but count != 0");

    assert property (@(posedge clk) disable iff (!rst_) ((count == 0) -> empty_flag))
      else $error("EMPTY_FLAG: count==0 but empty_flag not high");
  end

  if (STRICT_FULL) begin
    assert property (@(posedge clk) disable iff (!rst_) (full_flag -> (count == depth)))
      else $error("FULL_FLAG: full_flag high but count != depth");

    assert property (@(posedge clk) disable iff (!rst_) ((count == depth) -> full_flag))
      else $error("FULL_FLAG: count==depth but full_flag not high");
  end

  // Mutual exclusion (cannot be both full and empty unless depth==0)
  assert property (@(posedge clk) disable iff (!rst_) !(full_flag && empty_flag))
    else $error("FLAGS: full_flag and empty_flag both set");

  // ------------------------------------------------------------
  // 4. Count evolution rules
  // ------------------------------------------------------------
  // Using eff_read/eff_write to express spec; net delta must match
  assert property (@(posedge clk) disable iff (!rst_)
     $past(rst_) && rst_ |-> (count == ($past(count)
        + (eff_write ? 1 : 0)
        - (eff_read  ? 1 : 0))))
    else $error("COUNT_UPDATE: count not updated per effective read/write");

  // No change in idle
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en==0 && read_en==0) |-> count == $past(count))
    else $error("COUNT_IDLE: count changed during idle");

  // Write-only increment (when actually accepted)
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en && !read_en && (count < depth)) |-> count == $past(count)+1)
    else $error("COUNT_WRITE: write-only did not increment");

  // Read-only decrement (when actually accepted)
  assert property (@(posedge clk) disable iff (!rst_)
     (read_en && !write_en && (count > 0)) |-> count == $past(count)-1)
    else $error("COUNT_READ: read-only did not decrement");

  // Simultaneous read+write in mid occupancy leaves count unchanged
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en && read_en && count > 0 && count < depth) |-> count == $past(count))
    else $error("COUNT_RW_MID: count changed during simultaneous mid-occupancy");

  // Simultaneous at empty acts as write
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en && read_en && $past(count)==0) |-> count == 1)
    else $error("COUNT_RW_EMPTY: expected count=1 after write-only on empty");

  // Simultaneous at full acts as read
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en && read_en && $past(count)==depth) |-> count == depth-1)
    else $error("COUNT_RW_FULL: expected count=depth-1 after read-only on full");

  // ------------------------------------------------------------
  // 5. Pointer step rules (wr_ptr)
  // ------------------------------------------------------------
  // Write pointer increments iff an effective write occurs
  assert property (@(posedge clk) disable iff (!rst_)
     (eff_write) |-> (wr_ptr == $past(wr_ptr)+1))
    else $error("WR_PTR: did not increment on effective write");

  assert property (@(posedge clk) disable iff (!rst_)
     (!eff_write) |-> (wr_ptr == $past(wr_ptr)))
    else $error("WR_PTR: incremented without an effective write");

  // Read pointer increments iff an effective read occurs
  assert property (@(posedge clk) disable iff (!rst_)
     (eff_read) |-> (rd_ptr == $past(rd_ptr)+1))
    else $error("RD_PTR: did not increment on effective read");

  assert property (@(posedge clk) disable iff (!rst_)
     (!eff_read) |-> (rd_ptr == $past(rd_ptr)))
    else $error("RD_PTR: incremented without an effective read");

  // ------------------------------------------------------------
  // 6. No overflow / underflow semantic events
  //   (If an attempted write when full (and not simultaneous read) occurs,
  //    count and wr_ptr must stay.)
  // ------------------------------------------------------------
  assert property (@(posedge clk) disable iff (!rst_)
     (write_en && !read_en && (count == depth)) |-> (count == $past(count) && wr_ptr == $past(wr_ptr)))
    else $error("OVERFLOW_ATTEMPT: state changed on disallowed write");

  assert property (@(posedge clk) disable iff (!rst_)
     (read_en && !write_en && (count == 0)) |-> (count == $past(count) && rd_ptr == $past(rd_ptr)))
    else $error("UNDERFLOW_ATTEMPT: state changed on disallowed read");

  // ------------------------------------------------------------
  // 7. Occupancy invariant using cumulative counters
  // ------------------------------------------------------------
  int unsigned w_total, r_total;
  always_ff @(posedge clk or negedge rst_) begin
    if (!rst_) begin
      w_total <= 0;
      r_total <= 0;
    end else begin
      if (eff_write) w_total <= w_total + 1;
      if (eff_read)  r_total <= r_total + 1;
    end
  end

  assert property (@(posedge clk) disable iff (!rst_)
      count == (w_total - r_total))
    else $error("OCCUPANCY_INVARIANT: count mismatch with cumulative diff");

  assert property (@(posedge clk) disable iff (!rst_) (w_total - r_total) <= depth)
    else $error("OCCUPANCY_CAP: occupancy exceeded depth");

  // ------------------------------------------------------------
  // 8. Data integrity (FIFO ordering)
  // Model queue in assertions domain (not synthesizable)
  // ------------------------------------------------------------
  logic [width-1:0] model_q[$];

  // Update the model
  always_ff @(posedge clk or negedge rst_) begin
    if (!rst_) begin
      model_q.delete();
    end else begin
      if (eff_write) model_q.push_back(data_in);
      if (eff_read && model_q.size() > 0) model_q.pop_front();
    end
  end

  // When a read occurs (effective), data_out should equal the element
  // that was at the front just before the pop. Use sampled value.
  logic [width-1:0] expected_front;
  always_comb expected_front = (model_q.size() > 0) ? model_q[0] : 'x;

  // Because the design outputs combinationally from mem[rd_ptr], we check
  // data_out in the cycle of read_en (after pointer increments you may want
  // to shift one cycle if your memory infers synchronous read).
  property fifo_order_p;
    @(posedge clk) disable iff (!rst_)
      (eff_read && model_q.size()>0) |-> (data_out == $past(expected_front));
  endproperty

  assert property (fifo_order_p)
    else $error("FIFO_ORDER: data_out not matching expected sequence");

  // ------------------------------------------------------------
  // 9. Optional: data_out stable when no read pointer change
  // (May fail if a write overwrites current rd_ptr location prematurely in buggy variant)
  // ------------------------------------------------------------
  assert property (@(posedge clk) disable iff (!rst_)
     (rd_ptr == $past(rd_ptr)) |-> $stable(data_out))
    else $warning("DATA_OUT_STABLE: data_out changed without rd_ptr move (check design intent)");

endmodule

// Example bind (place in a separate non-synth file or testbench):
// bind black_box black_box_sva #(.depth(depth), .width(width)) black_box_sva_i (.*);