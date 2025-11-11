// SVA checker for fifo_buffer. Bind this to the DUT.
// Notes: These assertions model the intended FIFO behavior:
// - count must be in [0:BUFFER_SIZE]
// - accepted write/read are wr_en && !full / rd_en && !empty
// - count updates by +1/-1/0 accordingly
// - head/tail only advance on accepted ops and wrap properly
// - data integrity: read data equals oldest written data
// These checks will flag width/logic issues (e.g., count must be able to reach BUFFER_SIZE).

module fifo_buffer_sva #(parameter int BUFFER_SIZE = 16) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        wr_en,
  input  logic        rd_en,
  input  logic [7:0]  data_in,
  input  logic [7:0]  data_out,
  input  logic        empty,
  input  logic        full,
  // internal state (connect via bind to DUT internals)
  input  logic [31:0] head,
  input  logic [31:0] tail,
  input  logic [31:0] count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Convenience
  wire aw = wr_en && !full;   // accepted write
  wire ar = rd_en && !empty;  // accepted read

  // Reset state
  assert property (!rst_n |-> (head==0 && tail==0 && count==0));

  // Flags reflect count
  assert property (empty == (count == 0));
  assert property (full  == (count == BUFFER_SIZE));

  // Count bounds
  assert property (count <= BUFFER_SIZE);

  // Count update semantics
  assert property (1'b1 |-> $past(count) + (aw?1:0) - (ar?1:0) == count);

  // When both accepted in same cycle, occupancy stable
  assert property ((aw && ar) |-> count == $past(count));

  // No effect on illegal attempts
  assert property ((full && wr_en)  |-> (count == $past(count) && head == $past(head)));
  assert property ((empty && rd_en) |-> (count == $past(count) && tail == $past(tail) && $stable(data_out)));

  // Pointers advance only on accepted ops, with wrap
  assert property ( aw |-> head == (($past(head)==(BUFFER_SIZE-1)) ? 0 : $past(head)+1));
  assert property (!aw |-> head == $past(head));

  assert property ( ar |-> tail == (($past(tail)==(BUFFER_SIZE-1)) ? 0 : $past(tail)+1));
  assert property (!ar |-> tail == $past(tail));

  // Head/tail relation at empty/full
  assert property ((count==0)             |-> (head==tail));
  assert property ((count==BUFFER_SIZE)   |-> (head==tail));
  assert property (((count>0)&&(count<BUFFER_SIZE)) |-> (head!=tail));

  // Data_out only updates on accepted read
  assert property (!(rd_en && !empty) |-> $stable(data_out));

  // Simple reference model for ordering and occupancy
  byte unsigned q[$];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      q.delete();
    end else begin
      if (aw) q.push_back(data_in);
      if (ar) begin
        assert(q.size() > 0) else $error("FIFO underflow: read accepted when model empty");
        byte unsigned exp = q.pop_front();
        assert(data_out == exp) else $error("FIFO data mismatch: got %0h exp %0h", data_out, exp);
      end
      assert(q.size() == count) else $error("FIFO count mismatch: hw=%0d model=%0d", count, q.size());
    end
  end

  // Coverage
  cover property (empty ##1 aw);                              // first write from empty
  cover property (full);                                      // reach full
  cover property (aw && ar && (count>0) && (count<BUFFER_SIZE)); // simultaneous R/W in mid occupancy
  cover property (($past(head)==(BUFFER_SIZE-1)) && aw);      // head wrap
  cover property (($past(tail)==(BUFFER_SIZE-1)) && ar);      // tail wrap
  cover property (aw ##[1:$] ar);                             // write then later read same element path

endmodule

// Bind into DUT (connect internals explicitly)
bind fifo_buffer fifo_buffer_sva #(.BUFFER_SIZE(BUFFER_SIZE)) fifo_buffer_sva_i (
  .clk      (clk),
  .rst_n    (rst_n),
  .wr_en    (wr_en),
  .rd_en    (rd_en),
  .data_in  (data_in),
  .data_out (data_out),
  .empty    (empty),
  .full     (full),
  .head     (head),
  .tail     (tail),
  .count    (count)
);