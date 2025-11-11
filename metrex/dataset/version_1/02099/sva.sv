// SVA for BOR
// Bind example:
// bind BOR BOR_sva #(.RESET_DURATION(RESET_DURATION))
//   u_bor_sva(.clk(clk), .Vin(Vin), .Threshold(Threshold),
//             .Reset_en(Reset_en), .Reset(Reset),
//             .state(state), .counter(counter));

module BOR_sva #(parameter int RESET_DURATION = 10) (
  input  logic       clk,
  input  logic       Vin,
  input  logic       Threshold,
  input  logic       Reset_en,
  input  logic       Reset,
  input  logic [1:0] state,
  input  logic [7:0] counter
);
  localparam int N = RESET_DURATION;
  wire comparator_out = Vin & Threshold;

  default clocking cb @(posedge clk); endclocking

  // State encoding (only Idle=00 and Pulse=01 allowed when enabled)
  assert property (disable iff (!Reset_en)
                   (state inside {2'b00,2'b01}));

  // When disabled, next cycle must be fully cleared
  assert property ((!Reset_en) |=> (state==2'b00 && counter==8'd0 && !Reset));

  // Start condition: from idle with comparator_out, enter pulse state, raise Reset, clear counter
  assert property (disable iff (!Reset_en)
                   (state==2'b00 && comparator_out) |=> (state==2'b01 && Reset && counter==8'd0));

  // While in pulse and before terminal count, keep Reset high and increment counter by 1
  assert property (disable iff (!Reset_en)
                   (state==2'b01 && counter < N) |=> (state==2'b01 && Reset && counter == $past(counter)+1));

  // Terminal cycle: at exactly N, deassert Reset, return to idle, clear counter
  assert property (disable iff (!Reset_en)
                   (state==2'b01 && counter == N) |=> (state==2'b00 && !Reset && counter==8'd0));

  // Safety: counter must not exceed N while in pulse
  assert property (disable iff (!Reset_en)
                   (state==2'b01 |-> counter <= N));

  // Correlation: Reset high only in pulse state
  assert property (disable iff (!Reset_en)
                   (Reset |-> state==2'b01));

  // Pulse width: upon entering pulse state, Reset stays high for exactly N+1 cycles, then goes low
  assert property (disable iff (!Reset_en)
                   $rose(state==2'b01) |-> Reset[* (N+1)] ##1 !Reset);

  // No spurious activity in idle when comparator_out is low
  assert property (disable iff (!Reset_en)
                   (state==2'b00 && !comparator_out) |=> (state==2'b00 && !Reset));

  // Coverage
  cover property (disable iff (!Reset_en)
                  (state==2'b00 && comparator_out) ##1 state==2'b01
                  ##[1:N] (counter==N) ##1 (state==2'b00 && !Reset)); // full pulse

  cover property (state==2'b01 ##1 !Reset_en ##1 (!Reset && state==2'b00)); // aborted by disable

  cover property (disable iff (!Reset_en)
                  $rose(state==2'b01) ##[N+2:N+10] $rose(state==2'b01)); // back-to-back pulses
endmodule