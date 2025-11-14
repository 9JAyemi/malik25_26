// SVA for RetimeWrapper_580 and RetimeShiftRegister
// Focused, concise checks and coverage

// ---------------- Shift register assertions ----------------
module RetimeShiftRegister_sva #(parameter WIDTH=8, parameter STAGES=1)
(
  input  logic                     clock,
  input  logic                     reset,
  input  logic                     flow,
  input  logic [WIDTH-1:0]         in,
  input  logic [WIDTH-1:0]         out
);
  default clocking cb @ (posedge clock); endclocking

  // Asynchronous reset drives out to 0 immediately
  assert property (@(posedge reset) ##0 (out == '0));

  // While reset is high, out is 0 on every clock
  assert property (reset |-> (out == '0));

  // On a cycle after not-in-reset and flow=1, out updates from prior in
  assert property (disable iff (reset)
                   ($past(!reset) && $past(flow)) |-> out == $past(in));

  // On a cycle after not-in-reset and flow=0, out holds its value
  assert property (disable iff (reset)
                   ($past(!reset) && !$past(flow)) |-> out == $past(out));

  // Coverage: see both update and hold behaviors
  cover property (disable iff (reset) flow ##1 out == $past(in));
  cover property (disable iff (reset) !flow ##1 out == $past(out));
  cover property ($fell(reset));
endmodule

// ---------------- Wrapper assertions ----------------
module RetimeWrapper_580_sva
(
  input  logic         clock,
  input  logic         reset,
  input  logic [39:0]  io_in,
  input  logic [39:0]  io_out,
  input  logic [39:0]  sr_out_i,
  input  logic [39:0]  sr_in_i,
  input  logic         sr_flow_i,
  input  logic         sr_reset_i,
  input  logic         sr_clock_i
);
  default clocking cb @ (posedge clock); endclocking

  // Connectivity checks
  assert property (sr_clock_i == clock);
  assert property (sr_reset_i == reset);
  assert property (sr_in_i   == io_in);
  assert property (io_out    == sr_out_i);
  assert property (sr_flow_i == 1'b1);

  // Functional checks for the 1-stage retime with flow=1
  // Asynchronous reset drives output to 0 immediately
  assert property (@(posedge reset) ##0 (io_out == '0));
  // While reset is high, io_out is 0 on every clock
  assert property (reset |-> (io_out == '0));
  // One-cycle delay after coming out of reset
  assert property (disable iff (reset) $past(!reset) |-> io_out == $past(io_in));

  // Coverage: reset sequence and data propagation
  cover property ($fell(reset));
  cover property (disable iff (reset) $changed(io_in) ##1 (io_out == $past(io_in)));
endmodule

// ---------------- Binds ----------------
bind RetimeShiftRegister RetimeShiftRegister_sva #(.WIDTH(WIDTH), .STAGES(STAGES))
  u_RetimeShiftRegister_sva(.clock(clock), .reset(reset), .flow(flow), .in(in), .out(out));

bind RetimeWrapper_580 RetimeWrapper_580_sva
  u_RetimeWrapper_580_sva(.clock(clock), .reset(reset), .io_in(io_in), .io_out(io_out),
                          .sr_out_i(sr_out), .sr_in_i(sr_in), .sr_flow_i(sr_flow),
                          .sr_reset_i(sr_reset), .sr_clock_i(sr_clock));