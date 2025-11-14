// SVA for soc_system_jtag_uart_sim_scfifo_w
// Focus: safety, functional correctness, ordering, and key coverages.
// Bind this file to the DUT.

module soc_system_jtag_uart_sim_scfifo_w_sva
(
  input  logic        clk,
  input  logic        fifo_wr,
  input  logic [7:0]  fifo_wdata,
  input  logic        fifo_FF,
  input  logic        wfifo_empty,
  input  logic [5:0]  wfifo_used,
  input  logic [7:0]  r_dat,

  // internal state
  input  logic [5:0]  head,
  input  logic [5:0]  tail,
  input  logic [6:0]  count
);

  localparam int DEPTH = 64;

  default clocking cb @(posedge clk); endclocking

  // Basic well-formedness
  assert property (! $isunknown({count, head, tail, fifo_wr, fifo_wdata, fifo_FF, wfifo_empty, wfifo_used})))
    else $error("Unknown/X detected on key signals");

  // Count range (0..DEPTH)
  assert property (count <= DEPTH)
    else $error("Count out of range");

  // Flag/output correctness (combinational from current count)
  assert property (fifo_FF == (count == DEPTH))
    else $error("fifo_FF mismatch");
  assert property (wfifo_empty == (count == 0))
    else $error("wfifo_empty mismatch");
  assert property (wfifo_used == count[5:0])
    else $error("wfifo_used mismatch (truncation)");


  // Define accept conditions as they apply to state updates (use previous-cycle state)
  // A write is accepted iff fifo_wr was high and not full in the prior state.
  // A read is performed every cycle the prior state was not empty.
  // Note: These are the intended semantics of the gating.
  sequence w_acc;  $past(fifo_wr) && ($past(count) != DEPTH); endsequence
  sequence r_acc;  ($past(count) != 0);                        endsequence

  // Pointer update rules
  assert property (head == $past(head) + (w_acc ? 6'd1 : 6'd0))
    else $error("Head update incorrect");

  assert property (tail == $past(tail) + (r_acc ? 6'd1 : 6'd0))
    else $error("Tail update incorrect");

  // Count update rule (net +1 on accepted write, -1 on read). This will flag any last-assignment-wins bugs.
  assert property (count == ($past(count)
                             + (w_acc ? 7'd1 : 7'd0)
                             - (r_acc ? 7'd1 : 7'd0)))
    else $error("Count update incorrect");

  // Stability when idle (no write accepted and no read performed)
  assert property ((!w_acc && !r_acc) |-> (head == $past(head) && tail == $past(tail) && count == $past(count)))
    else $error("State changed without read/write");

  // No overflow and no underflow effects
  assert property (($past(count) == DEPTH && $past(fifo_wr)) |-> (head == $past(head)))
    else $error("Head advanced on write while full");
  assert property (($past(count) == 0) |-> (tail == $past(tail)))
    else $error("Tail advanced while empty");

  // Data ordering: every accepted write eventually emerges at the read with same value.
  // When the read of the recorded index happens (r_acc with $past(tail)==idx), r_dat in the next cycle must match.
  property p_write_to_read_order;
    bit [5:0] idx;
    bit [7:0] val;
    ($past(1'b1), // align sampling
     $past(1'b1)) throughout 1'b1 ##0
    ((fifo_wr && (count != DEPTH)), idx = head, val = fifo_wdata)
    |-> ##[1:$] ((r_acc && ($past(tail) == idx)) ##1 (r_dat == val));
  endproperty
  assert property (p_write_to_read_order)
    else $error("FIFO data ordering/integrity violated");

  // Coverages (key scenarios)
  // Accepted write
  cover property ($past(fifo_wr) && ($past(count) != DEPTH));
  // Performed read
  cover property ($past(count) != 0);
  // Simultaneous accepted write and read in same cycle
  cover property (($past(fifo_wr) && ($past(count) != DEPTH)) && ($past(count) != 0));
  // Become non-empty
  cover property ($rose(count != 0));
  // Become empty
  cover property ($rose(count == 0));
  // Pointer wrap-around
  cover property ($past(head) == 6'd63 && head == 6'd0);
  cover property ($past(tail) == 6'd63 && tail == 6'd0);

endmodule

bind soc_system_jtag_uart_sim_scfifo_w soc_system_jtag_uart_sim_scfifo_w_sva
(
  .clk(clk),
  .fifo_wr(fifo_wr),
  .fifo_wdata(fifo_wdata),
  .fifo_FF(fifo_FF),
  .wfifo_empty(wfifo_empty),
  .wfifo_used(wfifo_used),
  .r_dat(r_dat),
  .head(head),
  .tail(tail),
  .count(count)
);