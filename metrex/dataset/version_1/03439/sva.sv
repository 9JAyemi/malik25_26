// SVA checker for Depulser
module Depulser_sva (
  input logic        clock,
  input logic        reset,
  input logic        io_in,
  input logic        io_rst,
  input logic        io_out,

  input logic        r_clock,
  input logic        r_reset,
  input logic        r_io_in,
  input logic        r_io_out,
  input logic        r_io_enable,
  input logic [1:0]  state,
  input logic        pulse
);

  // Basic wiring equivalences (sanity of wrappers)
  assert property (@(posedge r_clock) r_clock == clock);
  assert property (@(posedge r_clock) r_reset == reset);
  assert property (@(posedge r_clock) io_out == r_io_out);

  // Combinational definitions
  assert property (@(posedge r_clock) r_io_in == (io_rst ? 1'b0 : io_in));
  assert property (@(posedge r_clock) r_io_enable == (io_in | io_rst));
  assert property (@(posedge r_clock) pulse == (r_io_in && (state == 2'b00)));

  // Asynchronous reset effects (must hold while reset is 1)
  assert property (@(posedge r_clock) r_reset |-> (r_io_out == 1'b0 && state == 2'b00));

  // State legality
  assert property (@(posedge r_clock) disable iff (r_reset)
                   state inside {2'b00, 2'b01, 2'b10});

  // One-shot behavior when a pulse is detected
  // pulse -> next: out=1, state=01 -> next: out=0, state=10 -> next: state=00
  assert property (@(posedge r_clock) disable iff (r_reset)
                   pulse |=> (r_io_out && state==2'b01)
                        ##1 (!r_io_out && state==2'b10)
                        ##1 (state==2'b00));

  // Phase 01 must last exactly one cycle and force out=0 on exit
  assert property (@(posedge r_clock) disable iff (r_reset)
                   (state==2'b01) |=> (!r_io_out && state==2'b10));

  // Phase 10 must last exactly one cycle, pass-through r_io_in, then return to 00
  assert property (@(posedge r_clock) disable iff (r_reset)
                   (state==2'b10) |=> (state==2'b00 && r_io_out == $past(r_io_in)));

  // Idle 00 without pulse: pass-through
  assert property (@(posedge r_clock) disable iff (r_reset)
                   (state==2'b00 && !pulse) |=> (state==2'b00 && r_io_out == $past(r_io_in)));

  // Covers
  cover property (@(posedge r_clock) disable iff (r_reset)
                  pulse ##1 (state==2'b01) ##1 (state==2'b10) ##1 (state==2'b00));

  cover property (@(posedge r_clock) disable iff (r_reset)
                  (state==2'b10) ##1 (state==2'b00 && r_io_out == $past(r_io_in)));

  cover property (@(posedge r_clock)
                  (io_rst && io_in && r_io_in==1'b0));

endmodule

// Bind into DUT
bind Depulser Depulser_sva depulser_sva_i (
  .clock(clock),
  .reset(reset),
  .io_in(io_in),
  .io_rst(io_rst),
  .io_out(io_out),

  .r_clock(r_clock),
  .r_reset(r_reset),
  .r_io_in(r_io_in),
  .r_io_out(r_io_out),
  .r_io_enable(r_io_enable),
  .state(state),
  .pulse(pulse)
);