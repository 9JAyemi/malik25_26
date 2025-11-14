// SVA for fifo_buffer. Bind into DUT to access internal pointers.
module fifo_buffer_sva #(
  parameter int DEPTH = 16,
  parameter int WIDTH = 16,
  localparam int PTRW = $clog2(DEPTH)
)(
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  wr_en,
  input  logic                  rd_en,
  input  logic [WIDTH-1:0]      data_in,
  input  logic [WIDTH-1:0]      data_out,
  input  logic                  empty,
  input  logic                  full,
  input  logic [3:0]            count,

  // internal pointers from DUT (bind to these)
  input  logic [PTRW-1:0]       head,
  input  logic [PTRW-1:0]       tail
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic [PTRW-1:0] inc_ptr (input [PTRW-1:0] p);
    inc_ptr = (p == PTRW'(DEPTH-1)) ? '0 : (p + 1'b1);
  endfunction

  // Handshake qualified by DUT’s own flags (mirrors hardware behavior)
  wire wr_ok = wr_en && !full;
  wire rd_ok = rd_en && !empty;

  // Reset state (synchronous in DUT)
  assert property (@(posedge clk) rst |-> (head=='0 && tail=='0 && count==0 && empty && !full));

  // Flag consistency w.r.t. count
  assert property (empty == (count==0));
  assert property (full  == (count==DEPTH)); // Will flag the 4-bit count/DEPTH=16 bug

  // Count update (arith on unbounded ints to catch overflow/underflow)
  assert property ($unsigned(count) == $unsigned($past(count)) + (wr_ok?1:0) - (rd_ok?1:0));

  // No op when operation is disallowed
  assert property (wr_en && full  |=> head==$past(head) && count==$past(count));
  assert property (rd_en && empty |=> tail==$past(tail) && $stable(data_out));

  // Pointer updates
  assert property (wr_ok && !rd_ok |=> head == inc_ptr($past(head)));
  assert property (!wr_ok          |=> head == $past(head));
  assert property (rd_ok && !wr_ok |=> tail == inc_ptr($past(tail)));
  assert property (!rd_ok          |=> tail == $past(tail));

  // Simultaneous read/write
  assert property (wr_ok && rd_ok |=> head==inc_ptr($past(head)) &&
                                   tail==inc_ptr($past(tail)) &&
                                   count==$past(count));

  // Head/Tail relation: equal only when empty or full
  assert property ((head==tail) |-> (empty || full));

  // Data integrity and reference model (cycle-accurate against DUT’s acceptance)
  bit [WIDTH-1:0] q[$];

  always_ff @(posedge clk) begin
    if (rst) begin
      q.delete();
    end else begin
      if (rd_ok) begin
        assert (q.size()>0) else $error("FIFO underflow vs model");
        if (q.size()>0) begin
          assert (data_out == q[0]) else $error("FIFO data order mismatch");
          void'(q.pop_front());
        end
      end
      if (wr_ok) q.push_back(data_in);

      assert ($unsigned(count) == q.size()) else $error("count != model size");
      assert (empty == (q.size()==0)) else $error("empty flag mismatch vs model");
      assert (full  == (q.size()==DEPTH)) else $error("full flag mismatch vs model");
    end
  end

  // Sanity/X checks
  assert property (!$isunknown({empty, full, count})));
  assert property (rd_ok |-> !$isunknown(data_out));

  // Coverage: key scenarios
  cover property (empty && wr_ok ##1 !empty);                       // leave empty
  cover property (count==1 && rd_ok ##1 empty);                     // become empty
  cover property (wr_ok && rd_ok);                                  // simultaneous R/W
  cover property (head==PTRW'(DEPTH-1) && wr_ok ##1 head=='0);      // head wrap
  cover property (tail==PTRW'(DEPTH-1) && rd_ok ##1 tail=='0);      // tail wrap
  cover property (empty ##[1:$] full);                              // fill to full
  cover property (full  ##[1:$] empty);                             // drain to empty

endmodule

// Bind example (place in a separate file or a testbench package):
// bind fifo_buffer fifo_buffer_sva #(.DEPTH(DEPTH), .WIDTH(16))
//   fifo_buffer_sva_i (.*, .head(head), .tail(tail));