// SVA checker for fifo_buffer. Bind this to the DUT.
module fifo_buffer_sva #(parameter int DW=8, DEPTH=16, AW=4)
(
  input logic                  clk,
  input logic                  reset,
  input logic [DW-1:0]         data_in,
  input logic                  write,
  input logic                  read,
  input logic [DW-1:0]         data_out,
  input logic                  empty,
  input logic                  full,
  // bind to DUT internals
  input logic [AW-1:0]         head,
  input logic [AW-1:0]         tail,
  input logic [AW-1:0]         count
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Golden model (occupancy + data ordering). Accepts ops iff 0<=occ<=DEPTH.
  int unsigned                      occ;
  logic [DW-1:0]                    q[$];
  wire                              inc_spec = write && (occ < DEPTH);
  wire                              dec_spec = read  && (occ > 0);
  logic [DW-1:0]                    exp_dout;

  // Model update
  always_ff @(posedge clk) begin
    if (reset) begin
      occ <= 0;
      q.delete();
      exp_dout <= '0;
    end else begin
      if (inc_spec) q.push_back(data_in);
      if (dec_spec) begin
        exp_dout <= q[0];
        void'(q.pop_front());
      end
      occ <= occ + (inc_spec?1:0) - (dec_spec?1:0);
    end
  end

  // Helpers
  function automatic [AW-1:0] bump(input [AW-1:0] p);
    return (p == DEPTH-1) ? '0 : p + 1'b1;
  endfunction

  // Reset result (synchronous)
  assert property (reset |=> head==0 && tail==0 && count==0 && empty && !full);

  // Flags must reflect golden occupancy
  assert property (empty == (occ==0));
  assert property (full  == (occ==DEPTH));

  // Count must equal golden occupancy (catches width/overflow bugs)
  assert property (count == occ);

  // Pointer updates must follow accepted operations
  assert property (inc_spec |=> head == bump($past(head)));
  assert property (!inc_spec |=> $stable(head));

  assert property (dec_spec |=> tail == bump($past(tail)));
  assert property (!dec_spec |=> $stable(tail));

  // Simultaneous accepted R/W leaves occupancy (and thus count) unchanged
  assert property (inc_spec && dec_spec |=> count == $past(count));

  // No side effects on underflow/overflow attempts
  assert property (read && (occ==0)    |=> $stable(count) && $stable(tail) && $stable(data_out));
  assert property (write && (occ==DEPTH) |=> $stable(count) && $stable(head));

  // FIFO data ordering: next-cycle data_out must equal oldest queued data on accepted read
  assert property (dec_spec |=> data_out == $past(exp_dout));

  // Pointer/occupancy consistency (modulo arithmetic)
  assert property ( (occ != DEPTH) |-> (((head - tail) & (DEPTH-1)) == occ) );
  assert property ( (occ == DEPTH) |-> (head == tail) );

  // Flags cannot both be asserted
  assert property (!(full && empty));

  // Coverage
  cover property (reset ##1 !reset ##1 occ==0);
  cover property ((occ==0) ##1 inc_spec[*DEPTH] ##1 (occ==DEPTH));        // fill to full
  cover property ((occ==DEPTH) ##1 dec_spec[*DEPTH] ##1 (occ==0));        // drain to empty
  cover property (inc_spec && ($past(head)==DEPTH-1) ##1 (head==0));      // head wrap
  cover property (dec_spec && ($past(tail)==DEPTH-1) ##1 (tail==0));      // tail wrap
  cover property (inc_spec && dec_spec);                                  // simultaneous R/W
  cover property (write && (occ==DEPTH));                                 // overflow attempt
  cover property (read  && (occ==0));                                     // underflow attempt

endmodule

// Bind to the DUT (tools permitting hierarchical binds to internal regs)
bind fifo_buffer fifo_buffer_sva #(.DW(8), .DEPTH(16), .AW(4)) u_fifo_buffer_sva (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .write(write),
  .read(read),
  .data_out(data_out),
  .empty(empty),
  .full(full),
  .head(head),
  .tail(tail),
  .count(count)
);