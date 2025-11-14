// SVA for async_fifo
// Bind this module to the DUT to check invariants, handshakes, flags, and basic coverage.
module async_fifo_sva #(
  parameter int F_WIDTH = 4,
  parameter int F_MAX   = 32
)(
  input  logic         i_wclk,
  input  logic         i_rclk,
  input  logic         i_reset,
  input  logic         i_push,
  input  logic         i_pop,
  input  logic         o_full,
  input  logic         o_empty,
  input  logic [F_WIDTH-1:0] write_pos,
  input  logic [F_WIDTH-1:0] read_pos,
  input  logic [7:0]   write_counter,
  input  logic [7:0]   read_counter,
  input  logic [65:0]  o_rdata
);

  // Static parameter consistency (depth vs full threshold)
  initial assert (F_MAX == (1<<F_WIDTH))
    else $error("F_MAX (%0d) must equal FIFO depth (1<<F_WIDTH=%0d)", F_MAX, (1<<F_WIDTH));

  // Local helpers
  function automatic int unsigned occ_cur();
    // 8-bit modulo occupancy used by DUT
    occ_cur = (write_counter - read_counter) & 'hFF;
  endfunction

  logic w_acc, r_acc;
  always_comb begin
    w_acc = i_push && !o_full;
    r_acc = i_pop  && !o_empty;
  end

  // Reset behavior (synchronous in the DUT)
  assert property (@(posedge i_wclk) i_reset |=> (write_counter==0 && write_pos==0));
  assert property (@(posedge i_rclk) i_reset |=> (read_counter==0  && read_pos==0));

  // Handshake effects on write domain
  assert property (@(posedge i_wclk) disable iff (i_reset)
    w_acc |=> (write_counter == $past(write_counter)+1 && write_pos == $past(write_pos)+1));
  assert property (@(posedge i_wclk) disable iff (i_reset)
   !w_acc |=> (write_counter == $past(write_counter)   && write_pos == $past(write_pos)));

  // Handshake effects on read domain
  assert property (@(posedge i_rclk) disable iff (i_reset)
    r_acc |=> (read_counter == $past(read_counter)+1 && read_pos == $past(read_pos)+1));
  assert property (@(posedge i_rclk) disable iff (i_reset)
   !r_acc |=> (read_counter == $past(read_counter)   && read_pos == $past(read_pos)));

  // o_rdata only updates on accepted read (no spurious changes)
  assert property (@(posedge i_rclk) disable iff (i_reset)
    !r_acc |=> $stable(o_rdata));

  // Flags must reflect occupancy and be mutually exclusive
  assert property (@(posedge i_wclk or posedge i_rclk)
    (o_empty == (occ_cur()==0)));
  assert property (@(posedge i_wclk or posedge i_rclk)
    (o_full  == (occ_cur()==F_MAX)));
  assert property (@(posedge i_wclk or posedge i_rclk)
    !(o_full && o_empty));

  // Occupancy bounded
  assert property (@(posedge i_wclk or posedge i_rclk)
    occ_cur() <= F_MAX);

  // Monotonic occupancy updates per clock edge
  assert property (@(posedge i_wclk) disable iff (i_reset)
    w_acc |=> (occ_cur() == ($past(occ_cur())+1)));
  assert property (@(posedge i_rclk) disable iff (i_reset)
    r_acc |=> (occ_cur() == ($past(occ_cur())-1)));

  // No-ops at illegal requests
  assert property (@(posedge i_wclk) disable iff (i_reset)
    (i_push && o_full) |=> (write_counter==$past(write_counter) && write_pos==$past(write_pos)));
  assert property (@(posedge i_rclk) disable iff (i_reset)
    (i_pop  && o_empty) |=> (read_counter==$past(read_counter)  && read_pos==$past(read_pos)));

  // Pointer step equals counter step in each domain
  assert property (@(posedge i_wclk) disable iff (i_reset)
    (write_counter != $past(write_counter)) |-> (write_pos != $past(write_pos)));
  assert property (@(posedge i_rclk) disable iff (i_reset)
    (read_counter  != $past(read_counter))  |-> (read_pos  != $past(read_pos)));

  // Coverage: fill to full, drain to empty, pointer wrap-around on both domains
  cover property (@(posedge i_wclk) disable iff (i_reset)
    w_acc [*F_MAX] ##1 o_full);
  cover property (@(posedge i_rclk) disable iff (i_reset)
    r_acc [*F_MAX] ##1 o_empty);

  cover property (@(posedge i_wclk) disable iff (i_reset)
    w_acc && ($past(write_pos)=={F_WIDTH{1'b1}}) |=> (write_pos=={F_WIDTH{1'b0}}));
  cover property (@(posedge i_rclk) disable iff (i_reset)
    r_acc && ($past(read_pos) =={F_WIDTH{1'b1}}) |=> (read_pos =={F_WIDTH{1'b0}}));

endmodule

// Example bind (connect internal regs for assertions)
// bind async_fifo async_fifo_sva #(.F_WIDTH(F_WIDTH), .F_MAX(F_MAX)) fifo_sva (
//   .i_wclk(i_wclk), .i_rclk(i_rclk), .i_reset(i_reset),
//   .i_push(i_push), .i_pop(i_pop),
//   .o_full(o_full), .o_empty(o_empty),
//   .write_pos(write_pos), .read_pos(read_pos),
//   .write_counter(write_counter), .read_counter(read_counter),
//   .o_rdata(o_rdata)
// );