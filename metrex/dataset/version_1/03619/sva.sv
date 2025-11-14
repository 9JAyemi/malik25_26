// SystemVerilog Assertions for fifo
// Concise, high-signal-coverage checks and key cover properties.
// Bind this file to the DUT: bind fifo fifo_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DEPTH(DEPTH)) u_fifo_sva (.*);

module fifo_sva #(
  parameter DATA_WIDTH = 8,
  parameter ADDR_WIDTH = 1,
  parameter DEPTH      = 2
)(
  input  logic                     clk,
  input  logic                     reset,
  input  logic                     if_write_ce,
  input  logic [DATA_WIDTH-1:0]    if_write,
  input  logic                     if_read_ce,
  input  logic                     if_empty_n,
  input  logic [DATA_WIDTH-1:0]    if_dout,
  input  logic                     if_full_n,
  input  logic [ADDR_WIDTH:0]      write_ptr,
  input  logic [ADDR_WIDTH:0]      read_ptr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Helpers
  function automatic logic [ADDR_WIDTH:0] inc_ptr(input logic [ADDR_WIDTH:0] p);
    inc_ptr = (p == DEPTH-1) ? '0 : p + 1;
  endfunction

  // Reset state
  assert property (@(posedge clk) reset |=> (write_ptr == '0 && read_ptr == '0 && !if_empty_n && if_full_n))
    else $error("Reset state mismatch");

  // Pointer range safety (should never index mem out of bounds)
  assert property (write_ptr < DEPTH)
    else $error("write_ptr out of range");
  assert property (read_ptr  < DEPTH)
    else $error("read_ptr out of range");

  // Write pointer progression and wrap
  assert property (if_write_ce |=> write_ptr == inc_ptr($past(write_ptr)))
    else $error("write_ptr did not advance/wrap correctly");
  assert property (!if_write_ce |=> write_ptr == $past(write_ptr))
    else $error("write_ptr changed without write");

  // Read pointer progression and wrap
  assert property (if_read_ce |=> read_ptr == inc_ptr($past(read_ptr)))
    else $error("read_ptr did not advance/wrap correctly");
  assert property (!if_read_ce |=> read_ptr == $past(read_ptr))
    else $error("read_ptr changed without read");

  // Flag correctness vs pointers
  assert property (if_empty_n == (write_ptr != read_ptr))
    else $error("if_empty_n inconsistent with pointers");

  assert property (if_full_n == (inc_ptr(write_ptr) != read_ptr))
    else $error("if_full_n inconsistent with pointers (next write index)");


  // Protocol safety (environment/DUT): no write on full, no read on empty
  assert property (if_write_ce |-> if_full_n)
    else $error("Write attempted while full");
  assert property (if_read_ce  |-> if_empty_n)
    else $error("Read attempted while empty");

  // Read data should be known when performing a valid read
  assert property (if_read_ce && if_empty_n |-> !$isunknown(if_dout))
    else $error("if_dout unknown on valid read");

  // Simple reference model for data integrity (no under/overflow)
  logic [DATA_WIDTH-1:0] q[$];

  always_ff @(posedge clk) begin
    if (reset) begin
      q.delete();
    end else begin
      if (if_write_ce && if_full_n) q.push_back(if_write);
      if (if_read_ce && if_empty_n) begin
        assert (q.size() > 0) else $error("Model underflow");
        logic [DATA_WIDTH-1:0] exp = q[0];
        q.pop_front();
        assert (if_dout == exp)
          else $error("FIFO data mismatch exp=%0h got=%0h", exp, if_dout);
      end
      // Flags reflect model occupancy
      assert (if_empty_n == (q.size() != 0))
        else $error("if_empty_n disagrees with model occupancy");
      assert (if_full_n  == (q.size() != DEPTH))
        else $error("if_full_n disagrees with model capacity");
    end
  end

  // Coverage: fill to full, drain to empty, wrap, and simultaneous R/W
  cover property (if_full_n ##1 (if_write_ce, 1'b1)[*1:$] ##1 !if_full_n);
  cover property (if_empty_n ##1 (if_read_ce, 1'b1)[*1:$] ##1 !if_empty_n);
  cover property (if_write_ce && (write_ptr == DEPTH-1) ##1 (write_ptr == '0));
  cover property (if_read_ce  && (read_ptr  == DEPTH-1) ##1 (read_ptr  == '0));
  cover property (if_write_ce && if_read_ce);

endmodule