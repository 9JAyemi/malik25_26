// SVA for spi_master: concise, high-quality checks and coverage
// Bind this file to the DUT.
// Focus: protocol/state sequencing, counters/divider, shifting, and outputs.

module spi_master_sva #(
  parameter int CLK_DIVIDE = 3
) (
  input  logic                      clk,
  input  logic                      reset,

  // DUT ports
  input  logic                      spi_start,
  input  logic [7:0]                spi_data,
  input  logic                      spi_fin,
  input  logic                      spi_csn,
  input  logic                      spi_sdo,
  input  logic                      spi_sclk,

  // Internal DUT signals (bind to regs)
  input  logic [1:0]                spi_sm_state,
  input  logic [CLK_DIVIDE-1:0]     clk_divider,
  input  logic [7:0]                spi_data_shift,
  input  logic [2:0]                shift_counter
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  localparam int DIV_CYCLES = 1 << CLK_DIVIDE;
  localparam [CLK_DIVIDE-1:0] DIV_ALL_ONES = {CLK_DIVIDE{1'b1}};

  // Mirror DUT state encodings
  localparam [1:0] STATE_IDLE = 2'h0;
  localparam [1:0] STATE_SEND = 2'h1;
  localparam [1:0] STATE_HOLD = 2'h2;
  localparam [1:0] STATE_DONE = 2'h3;

  // Basic output equivalences
  assert property (spi_csn  == ((spi_sm_state==STATE_IDLE) && !spi_start));
  assert property (spi_sdo  == spi_data_shift[7]);
  assert property (spi_sclk == ((spi_sm_state==STATE_SEND) && clk_divider[CLK_DIVIDE-1]));
  assert property (spi_fin  == (spi_sm_state==STATE_DONE));

  // No X on key state/outputs post-reset
  assert property (!$isunknown({spi_sm_state,spi_csn,spi_sclk,spi_sdo,spi_fin}));

  // Reset values (async reset asserted)
  assert property (@(posedge clk) reset |-> (spi_sm_state==STATE_IDLE
                                          && clk_divider=='0
                                          && shift_counter=='0
                                          && spi_data_shift=='0));

  // IDLE behavior
  assert property ((spi_sm_state==STATE_IDLE && !spi_start) |=> spi_sm_state==STATE_IDLE);
  assert property ((spi_sm_state==STATE_IDLE && spi_start)
                   |=> (spi_sm_state==STATE_SEND
                        && clk_divider=='0
                        && shift_counter=='0
                        && spi_data_shift==$past(spi_data)));

  // SEND: clk_divider always increments
  assert property ((spi_sm_state==STATE_SEND) |=> clk_divider == $past(clk_divider)+1);

  // SEND: shift only on divider wrap; otherwise hold
  assert property ((spi_sm_state==STATE_SEND && $past(clk_divider)!=DIV_ALL_ONES)
                   |=> (shift_counter==$past(shift_counter)
                        && spi_data_shift==$past(spi_data_shift)
                        && spi_sm_state==STATE_SEND));

  assert property ((spi_sm_state==STATE_SEND && $past(clk_divider)==DIV_ALL_ONES && $past(shift_counter)!=3'd7)
                   |=> (shift_counter==$past(shift_counter)+1
                        && spi_data_shift==={$past(spi_data_shift)[6:0],1'b0}
                        && spi_sm_state==STATE_SEND));

  // SEND -> HOLD exactly after 8th shift (old shift_counter==7 at wrap)
  assert property ((spi_sm_state==STATE_SEND && $past(clk_divider)==DIV_ALL_ONES && $past(shift_counter)==3'd7)
                   |=> (spi_sm_state==STATE_HOLD
                        && shift_counter==$past(shift_counter)+1
                        && spi_data_shift==={$past(spi_data_shift)[6:0],1'b0}));

  // SDO stability between shifts in SEND
  assert property ((spi_sm_state==STATE_SEND && $past(clk_divider)!=DIV_ALL_ONES) |=> spi_sdo==$past(spi_sdo));

  // HOLD: clk_divider increments; leave HOLD only on wrap -> DONE
  assert property ((spi_sm_state==STATE_HOLD) |=> clk_divider == $past(clk_divider)+1);
  assert property ((spi_sm_state==STATE_HOLD && $past(clk_divider)!=DIV_ALL_ONES) |=> spi_sm_state==STATE_HOLD);
  assert property ((spi_sm_state==STATE_HOLD && $past(clk_divider)==DIV_ALL_ONES) |=> spi_sm_state==STATE_DONE);

  // DONE: stay until spi_start deasserts, then back to IDLE
  assert property ((spi_sm_state==STATE_DONE && spi_start)  |=> spi_sm_state==STATE_DONE);
  assert property ((spi_sm_state==STATE_DONE && !spi_start) |=> spi_sm_state==STATE_IDLE);

  // Illegal transitions guard (one-hot of allowed next states)
  assert property (
    (spi_sm_state==STATE_IDLE) |=> (spi_sm_state inside {STATE_IDLE,STATE_SEND})
  );
  assert property (
    (spi_sm_state==STATE_SEND) |=> (spi_sm_state inside {STATE_SEND,STATE_HOLD})
  );
  assert property (
    (spi_sm_state==STATE_HOLD) |=> (spi_sm_state inside {STATE_HOLD,STATE_DONE})
  );
  assert property (
    (spi_sm_state==STATE_DONE) |=> (spi_sm_state inside {STATE_DONE,STATE_IDLE})
  );

  // Bounded liveness: a start in IDLE leads to FIN within 9*DIV_CYCLES cycles
  assert property ((spi_sm_state==STATE_IDLE && spi_start) |-> ##[1:(9*DIV_CYCLES)] spi_fin);

  // Coverage: full transaction path and behaviors
  cover property (
    (spi_sm_state==STATE_IDLE && spi_start)
    ##1 (spi_sm_state==STATE_SEND)
    ##[1:(8*DIV_CYCLES)] (shift_counter==3'd7 && $past(clk_divider)==DIV_ALL_ONES)
    ##1 (spi_sm_state==STATE_HOLD)
    ##[1:DIV_CYCLES] (spi_sm_state==STATE_DONE)
    ##1 (!spi_start && spi_sm_state==STATE_IDLE)
  );

  // Cover: sclk activity while sending
  cover property (spi_sm_state==STATE_SEND && spi_sclk);

  // Cover: start held high across DONE then dropped
  cover property (
    (spi_sm_state==STATE_IDLE && spi_start)
    ##1 (spi_sm_state==STATE_SEND)
    ##[1:(9*DIV_CYCLES)] (spi_sm_state==STATE_DONE && spi_start)
    ##1 (!spi_start && spi_sm_state==STATE_IDLE)
  );

endmodule

// Bind to DUT instance(s). Map internals for robust checking.
bind spi_master spi_master_sva #(.CLK_DIVIDE(CLK_DIVIDE)) spi_master_sva_i (
  .clk(clk),
  .reset(reset),

  .spi_start(spi_start),
  .spi_data(spi_data),
  .spi_fin(spi_fin),
  .spi_csn(spi_csn),
  .spi_sdo(spi_sdo),
  .spi_sclk(spi_sclk),

  .spi_sm_state(spi_sm_state),
  .clk_divider(clk_divider),
  .spi_data_shift(spi_data_shift),
  .shift_counter(shift_counter)
);