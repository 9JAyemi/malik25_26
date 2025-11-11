// SVA bind module for fifo
module fifo_sva #(
  parameter int WIDTH = 8,
  parameter int DEPTH = 12
)(
  input logic                      clk,
  input logic                      reset,

  input logic [WIDTH-1:0]          data_in,
  input logic                      data_in_start,
  input logic                      data_in_end,

  input logic [WIDTH-1:0]          data_out,
  input logic                      data_out_start,
  input logic                      data_out_end,

  input logic [WIDTH-1:0]          buffer [0:DEPTH-1],
  input logic [DEPTH-1:0]          read_ptr,
  input logic [DEPTH-1:0]          write_ptr,
  input logic [DEPTH-1:0]          count
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Shorthands for one-cycle-ago push/pop semantics used by DUT
  let PUSH = $past(data_in_start);
  let POP  = $past(data_out_end) && ($past(count) > 0);

  // Reset state
  assert property (reset |-> (read_ptr==0 && write_ptr==0 && count==0));

  // Fundamental invariants
  assert property (count <= DEPTH);                 // no overflow
  assert property (read_ptr < DEPTH);               // index in range
  assert property (write_ptr < DEPTH);              // index in range
  assert property (!$isunknown({data_out_start, data_out_end})); // flags known

  // Precise next-state relations (single concise checks)
  // Count = prev_count + push - pop
  assert property (1'b1 |-> count
                   == $past(count)
                      + (PUSH ? 1 : 0)
                      - (POP  ? 1 : 0));

  // Write pointer increments on push, otherwise stable
  assert property (1'b1 |-> write_ptr
                   == $past(write_ptr) + (PUSH ? 1 : 0));

  // Read pointer increments on pop, otherwise stable
  assert property (1'b1 |-> read_ptr
                   == $past(read_ptr) + (POP ? 1 : 0));

  // Index used for access must be in range at moment of access
  assert property (PUSH |-> $past(write_ptr) < DEPTH);
  assert property (POP  |-> $past(read_ptr)  < DEPTH);

  // Data_out update only on pop, with correct value; otherwise stable
  assert property (data_out
                   == (POP ? $past(buffer[$past(read_ptr)]) : $past(data_out)));
  // On a pop, data_out must be known
  assert property (POP |-> !$isunknown(data_out));

  // Flag behavior matches RTL (note: flags are driven from previous-cycle state)
  let EMPTYp = ($past(count) == 0);
  let FULLp  = ($past(count) == DEPTH);

  assert property (data_out_end
                   == (EMPTYp ? 1'b1
                              : (FULLp ? 1'b0
                                       : ($past(write_ptr) == DEPTH-1))));
  assert property (data_out_start
                   == (EMPTYp ? 1'b0
                              : (FULLp ? 1'b1
                                       : ($past(read_ptr) == 0))));

  // Underflow protection: no decrement/pop effect when empty
  assert property (($past(count)==0 && $past(data_out_end))
                   |-> (count==$past(count) && read_ptr==$past(read_ptr)));

  // Coverage: key scenarios
  cover property (count==0 ##1 data_in_start ##1 count==1);                 // first push from empty
  cover property (count==DEPTH-1 ##1 data_in_start ##1 count==DEPTH);       // reach full
  cover property (data_in_start && $past(data_out_end) && $past(count>0));  // push and pop same cycle
  cover property (count>0 ##1 $past(data_out_end) && $past(count>0) ##1 count==$past(count)-1); // a pop
  cover property (read_ptr==0 && write_ptr==DEPTH-1);                       // both boundary pointers visible

endmodule

// Bind to all fifo instances (inherits parameters and connects by name)
bind fifo fifo_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH)) fifo_sva_i (.*);