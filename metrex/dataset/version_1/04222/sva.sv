// SVA for fifo_buffer
// Bind these assertions to the DUT

module fifo_buffer_sva
(
  input logic        wr_clk,
  input logic [1:0]  buffer,
  input logic [1:0]  next_buffer,
  input logic        full,
  input logic [0:0]  AS,
  input logic        out,
  input logic [0:0]  in0
);

  // Establish $past availability
  logic past_valid;
  always_ff @(posedge wr_clk) past_valid <= 1'b1;

  default clocking cb @(posedge wr_clk); endclocking

  // Combinational mappings
  a_full_def: assert property (full == (buffer[1] != 1'b0));
  a_as_map:   assert property (AS == full);
  a_out_map:  assert property (out == buffer[0]);

  // Registered dataflow relationships
  // buffer nonblocking assignment from prior next_buffer
  a_buf_follows_nb: assert property (past_valid |-> buffer == $past(next_buffer));

  // next_buffer update when not full (gated by previous-cycle full)
  a_nextbuf_update_writes: assert property (
    past_valid && !$past(full) |-> (next_buffer[1] == $past(buffer[0])) && (next_buffer[0] == $past(in0))
  );

  // next_buffer holds previous buffer when full
  a_nextbuf_hold_when_full: assert property (
    past_valid && $past(full) |-> next_buffer == $past(buffer)
  );

  // Outputs should be known after first cycle
  a_no_x_outputs: assert property (past_valid |-> !$isunknown({AS, out}));

  // Coverage
  c_full_trans:     cover property (past_valid && !full ##1 full);
  c_write_update:   cover property (past_valid && !$past(full)
                                    && (next_buffer[1] == $past(buffer[0]))
                                    && (next_buffer[0] == $past(in0)));
  c_out_changes:    cover property (past_valid && $changed(out));
  c_hold_when_full: cover property (past_valid && $past(full)
                                    && next_buffer == $past(buffer)
                                    && buffer == $past(next_buffer));

endmodule

bind fifo_buffer fifo_buffer_sva i_fifo_buffer_sva (
  .wr_clk(wr_clk),
  .buffer(buffer),
  .next_buffer(next_buffer),
  .full(full),
  .AS(AS),
  .out(out),
  .in0(in0)
);