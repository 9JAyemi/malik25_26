// SVA checker for fifo_buffer
// Bind this module to the DUT:  bind fifo_buffer fifo_buffer_sva chk(.*);

module fifo_buffer_sva(
  input logic          clock,
  input logic          ready,
  input logic  [7:0]   head,
  input logic          tail_req,
  input logic          tail_ack,
  input logic  [7:0]   tail_value,
  input logic          tail_value_valid,
  input logic          req,
  input logic          ack,
  input logic  [7:0]   value,
  input logic          value_valid,

  // internal DUT regs
  input logic  [7:0]   read_pointer,
  input logic  [7:0]   write_pointer,
  input logic          write_data,             // unused by checker
  input logic  [7:0]   write_pointer_next,
  input logic  [7:0]   read_pointer_next,
  input logic  [7:0]   read_data,
  input logic  [7:0]   tail_data,
  input logic  [7:0]   tail_pointer,
  input logic  [7:0]   tail_pointer_next,
  input logic  [7:0]   head_pointer,
  input logic  [7:0]   head_pointer_next,
  input logic  [7:0]   buffer_size,
  input logic  [7:0]   buffer_size_next,
  input logic          tail_full,
  input logic          head_full,
  input logic          tail_empty,
  input logic          head_empty
);

  default clocking cb @(posedge clock); endclocking

  // Helper conditions
  logic cond_head_write, cond_head_read, cond_tail_write, cond_tail_read, cond_head_out;
  always_comb begin
    cond_head_write = ready && !head_full && (head_pointer == write_pointer);
    cond_head_read  = ready && req && !head_empty && (read_pointer == head_pointer);
    cond_tail_write = ready && !tail_full && (tail_pointer == write_pointer) && tail_req;
    cond_tail_read  = ready && tail_value_valid && !tail_empty && (tail_pointer == read_pointer);
    cond_head_out   = (!head_empty && (head_pointer == read_pointer));
  end

  // Lightweight reference model for data correctness (by address)
  logic [7:0] model_mem [0:255];
  always @(posedge clock) begin
    if (cond_head_write)  model_mem[write_pointer] <= head;
    if (cond_tail_write)  model_mem[tail_pointer]  <= tail_data;
  end

  // Basic X checks on key outputs when claimed valid
  assert property (value_valid |-> !$isunknown({value, ack})));

  // Next-state mirrors must drive current-state (always_comb copies)
  assert property (write_pointer == write_pointer_next);
  assert property (read_pointer  == read_pointer_next);
  assert property (head_pointer  == head_pointer_next);
  assert property (tail_pointer  == tail_pointer_next);
  assert property (buffer_size   == buffer_size_next);

  // Hold behavior when not ready
  assert property (!ready |=> (write_pointer_next == $past(write_pointer_next) &&
                               read_pointer_next  == $past(read_pointer_next)  &&
                               head_pointer_next  == $past(head_pointer_next)  &&
                               tail_pointer_next  == $past(tail_pointer_next)  &&
                               buffer_size_next   == $past(buffer_size_next)   &&
                               tail_data          == $past(tail_data)));

  // Head write: increment and full computation
  assert property (cond_head_write |-> (write_pointer_next == write_pointer + 8'd1));
  assert property (cond_head_write |-> (head_full == (write_pointer_next == read_pointer)));

  // Head read: increment and empty computation
  assert property (cond_head_read |-> (read_pointer_next == read_pointer + 8'd1));
  assert property (cond_head_read |-> (head_empty == (read_pointer_next == write_pointer)));

  // Tail write: decrement and full computation
  assert property (cond_tail_write |-> (tail_pointer_next == tail_pointer - 8'd1));
  assert property (cond_tail_write |-> (tail_full == (tail_pointer_next == write_pointer)));

  // Tail read: decrement and empty computation
  assert property (cond_tail_read |-> (tail_pointer_next == tail_pointer - 8'd1));
  assert property (cond_tail_read |-> (tail_empty == (tail_pointer_next == write_pointer)));

  // No simultaneous conflicting writes or reads at the same index
  assert property (!(cond_head_write && cond_tail_write)); // both target write_pointer when tail_pointer==write_pointer
  assert property (!(cond_head_read  && cond_tail_read));  // both target read_pointer when head_pointer==tail_pointer

  // Output combinational correctness
  assert property (cond_head_out |-> (value == read_data && ack == tail_ack && value_valid == tail_value_valid));
  assert property (!cond_head_out |-> (value == 8'h00 && ack == 1'b0 && value_valid == 1'b0));
  assert property (ack |-> value_valid);

  // Buffer size invariants
  assert property (buffer_size < 8'd256);
  assert property (ready |-> buffer_size_next ==
                           ((head_pointer <= tail_pointer) ?
                              (tail_pointer - head_pointer) :
                              (8'd256 - head_pointer + tail_pointer)));

  // Data correctness on head-read (compares registered read_data with model)
  assert property (cond_head_read |=> (read_data == $past(model_mem[$past(read_pointer)])));

  // Flag sanity
  assert property (!(head_full && head_empty));
  assert property (!(tail_full && tail_empty));

  // Wrap-around coverage
  cover property (cond_head_write && (write_pointer == 8'hFF) ##1 (write_pointer_next == 8'h00));
  cover property (cond_tail_write && (tail_pointer  == 8'h00) ##1 (tail_pointer_next  == 8'hFF));

  // Functional coverage: exercise each basic operation
  cover property (cond_head_write);
  cover property (cond_head_read);
  cover property (cond_tail_write);
  cover property (cond_tail_read);

endmodule

// Example bind (instantiate in a package or tb):
// bind fifo_buffer fifo_buffer_sva chk(.*);