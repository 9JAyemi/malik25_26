// SVA for VGACtrl
package VGACtrl_sva_pkg;

  module VGACtrl_sva #(
    parameter int H_SYNC_PERIOD        = 96,
    parameter int H_SYNC_PULSE_WIDTH   = 16,
    parameter int V_SYNC_PERIOD        = 8000,
    parameter int V_SYNC_PULSE_WIDTH   = 2,
    parameter int DISPLAY_WIDTH        = 640,
    parameter int DISPLAY_HEIGHT       = 480
  )(
    input  logic        clk,
    input  logic        reset,
    input  logic        vga_h_sync,
    input  logic        vga_v_sync,
    input  logic        inDisplayArea,
    input  logic [9:0]  CounterX,
    input  logic [9:0]  CounterY,
    input  logic [9:0]  h_counter,
    input  logic [9:0]  v_counter
  );

    default clocking cb @(posedge clk); endclocking
    default disable iff (reset);

    // No X/Z during normal operation
    assert property (!$isunknown({vga_h_sync, vga_v_sync, inDisplayArea,
                                  CounterX, CounterY, h_counter, v_counter}));

    // While reset is asserted at a clock edge, all state/outputs held at 0
    assert property (disable iff (1'b0) @(posedge clk)
                     reset |-> (h_counter==0 && v_counter==0 &&
                                vga_h_sync==0 && vga_v_sync==0 &&
                                inDisplayArea==0 && CounterX==0 && CounterY==0));

    // Counters stay within display range
    assert property (h_counter < DISPLAY_WIDTH);
    assert property (v_counter < DISPLAY_HEIGHT);

    // Monotonic increment and wrap
    assert property ((h_counter != DISPLAY_WIDTH-1) |=> h_counter == $past(h_counter)+1);
    assert property ((h_counter == DISPLAY_WIDTH-1) |=> h_counter == 0);
    assert property ((v_counter != DISPLAY_HEIGHT-1) |=> v_counter == $past(v_counter)+1);
    assert property ((v_counter == DISPLAY_HEIGHT-1) |=> v_counter == 0);

    // Output counters track internal counters (1-cycle latency)
    assert property (CounterX == $past(h_counter) || $past(reset));
    assert property (CounterY == $past(v_counter) || $past(reset));
    assert property (CounterX < DISPLAY_WIDTH);
    assert property (CounterY < DISPLAY_HEIGHT);

    // Sync outputs match combinational intents
    assert property (vga_h_sync == (h_counter >= (DISPLAY_WIDTH - H_SYNC_PULSE_WIDTH)));
    assert property (vga_v_sync == (v_counter >= (DISPLAY_HEIGHT - V_SYNC_PULSE_WIDTH)));

    // Sync pulse alignment, width, and end points
    assert property ($rose(vga_h_sync) |-> h_counter == (DISPLAY_WIDTH - H_SYNC_PULSE_WIDTH));
    assert property ($rose(vga_h_sync) |-> vga_h_sync[*H_SYNC_PULSE_WIDTH] ##1 !vga_h_sync);
    assert property ($fell(vga_h_sync) |-> h_counter == 0);

    assert property ($rose(vga_v_sync) |-> v_counter == (DISPLAY_HEIGHT - V_SYNC_PULSE_WIDTH));
    assert property ($rose(vga_v_sync) |-> vga_v_sync[*V_SYNC_PULSE_WIDTH] ##1 !vga_v_sync);
    assert property ($fell(vga_v_sync) |-> v_counter == 0);

    // Display area mapping
    assert property (inDisplayArea == ((h_counter < DISPLAY_WIDTH) && (v_counter < DISPLAY_HEIGHT)));

    // Minimal, meaningful coverage
    cover property (h_counter == DISPLAY_WIDTH-1 ##1 h_counter == 0);
    cover property (v_counter == DISPLAY_HEIGHT-1 ##1 v_counter == 0);
    cover property ($rose(vga_h_sync));
    cover property ($rose(vga_v_sync));
    cover property (inDisplayArea && $rose(vga_h_sync));
    cover property (inDisplayArea && $rose(vga_v_sync));

  endmodule

endpackage

// Bind example (place in a bind file or a testbench)
import VGACtrl_sva_pkg::*;
bind VGACtrl VGACtrl_sva #(
  .H_SYNC_PERIOD(H_SYNC_PERIOD),
  .H_SYNC_PULSE_WIDTH(H_SYNC_PULSE_WIDTH),
  .V_SYNC_PERIOD(V_SYNC_PERIOD),
  .V_SYNC_PULSE_WIDTH(V_SYNC_PULSE_WIDTH),
  .DISPLAY_WIDTH(DISPLAY_WIDTH),
  .DISPLAY_HEIGHT(DISPLAY_HEIGHT)
) i_vgactrl_sva (
  .clk(clk),
  .reset(reset),
  .vga_h_sync(vga_h_sync),
  .vga_v_sync(vga_v_sync),
  .inDisplayArea(inDisplayArea),
  .CounterX(CounterX),
  .CounterY(CounterY),
  .h_counter(h_counter),
  .v_counter(v_counter)
);