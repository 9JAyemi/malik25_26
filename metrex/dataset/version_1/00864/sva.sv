// SVA for S4L2: checks divider, state machine, 7-seg mapping, and provides coverage.
module S4L2_sva #(parameter int unsigned DIV = 25_000_000)
(
  input  logic        clock_50mhz,
  input  logic        clock_1hz,
  input  logic [6:0]  segmentos,
  input  logic        anodo,
  input  logic [3:0]  estado,
  input  logic [25:0] cuenta_para_1hz
);

  // Clocking and past-valid guard
  default clocking cb @ (posedge clock_50mhz); endclocking
  logic past_valid;
  always_ff @(posedge clock_50mhz) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Helpers
  function automatic logic [3:0] next_state(input logic [3:0] s);
    return (s == 4'd15) ? 4'd0 : (s + 4'd1);
  endfunction

  function automatic logic [6:0] seg_of(input logic [3:0] s);
    case (s)
      4'd0:  seg_of = ~7'h3F;
      4'd1:  seg_of = ~7'h06;
      4'd2:  seg_of = ~7'h5B;
      4'd3:  seg_of = ~7'h4F;
      4'd4:  seg_of = ~7'h66;
      4'd5:  seg_of = ~7'h6D;
      4'd6:  seg_of = ~7'h7D;
      4'd7:  seg_of = ~7'h07;
      4'd8:  seg_of = ~7'h7F;
      4'd9:  seg_of = ~7'h6F;
      4'd10: seg_of = ~7'h77;
      4'd11: seg_of = ~7'h7C;
      4'd12: seg_of = ~7'h39;
      4'd13: seg_of = ~7'h5E;
      4'd14: seg_of = ~7'h79;
      4'd15: seg_of = ~7'h71;
      default: seg_of = 'x;
    endcase
  endfunction

  // Sanity/known checks
  assert property (!$isunknown({clock_1hz, anodo, estado, segmentos})));
  assert property (anodo == 1'b0);

  // Divider: counter behavior and clock_1hz period
  assert property (cuenta_para_1hz <= (DIV-1));
  assert property ( ($past(cuenta_para_1hz) < (DIV-1)) |->
                    (cuenta_para_1hz == $past(cuenta_para_1hz) + 1 && !$changed(clock_1hz)) );
  assert property ( ($past(cuenta_para_1hz) == (DIV-1)) |->
                    (cuenta_para_1hz == 0 && $changed(clock_1hz)) );
  assert property ( $changed(clock_1hz) |-> $past(cuenta_para_1hz) == (DIV-1) );
  // Exact half-period: a change followed by DIV-1 cycles stable, then a change
  assert property ( $changed(clock_1hz) |-> !$changed(clock_1hz)[*(DIV-1)] ##1 $changed(clock_1hz) );

  // State machine: range, update only on posedge of 1Hz, correct increment
  assert property (estado inside {[4'd0:4'd15]});
  assert property ( $changed(estado) |-> $rose(clock_1hz) );
  // On the 50MHz cycle after a 1Hz posedge, estado must be next_state(previous)
  assert property ( $rose(clock_1hz) |-> ##1 estado == next_state($past(estado)) );
  // No change on 1Hz falling edge
  assert property ( $fell(clock_1hz) |-> ##1 $stable(estado) );

  // 7-seg mapping must match estado
  assert property ( segmentos == seg_of(estado) );

  // Coverage
  // - See both edges of 1Hz and correct spacing
  cover property ( $rose(clock_1hz) );
  cover property ( $fell(clock_1hz) );
  cover property ( $changed(clock_1hz) ##(DIV) $changed(clock_1hz) ); // full period ~ 2*DIV half-cycles

  // - Hit all states and wrap 15->0
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_STATES
      cover property (estado == i[3:0]);
    end
  endgenerate
  cover property ( $rose(clock_1hz) && $past(estado) == 4'd15 ##1 estado == 4'd0 );

  // - Observe each segment pattern
  generate
    for (i = 0; i < 16; i++) begin : C_SEGS
      cover property (estado == i[3:0] && segmentos == seg_of(i[3:0]));
    end
  endgenerate

endmodule

// Bind to DUT (accesses internal cuenta_para_1hz)
bind S4L2 S4L2_sva #(.DIV(25_000_000)) S4L2_sva_i (
  .clock_50mhz(clock_50mhz),
  .clock_1hz(clock_1hz),
  .segmentos(segmentos),
  .anodo(anodo),
  .estado(estado),
  .cuenta_para_1hz(cuenta_para_1hz)
);