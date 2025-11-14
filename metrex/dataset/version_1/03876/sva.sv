// SVA for altera_up_rs232_counters
// Bind this file to the DUT to check/cover behavior

module altera_up_rs232_counters_sva #(
  parameter int CW                    = 9,
  parameter int BAUD_TICK_COUNT       = 433,
  parameter int HALF_BAUD_TICK_COUNT  = 216,
  parameter int TDW                   = 11
)(
  input  logic                 clk,
  input  logic                 reset,
  input  logic                 reset_counters,
  input  logic                 baud_clock_rising_edge,
  input  logic                 baud_clock_falling_edge,
  input  logic                 all_bits_transmitted,
  input  logic [CW-1:0]        baud_counter,
  input  logic [3:0]           bit_counter
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial begin
    assert (BAUD_TICK_COUNT < (1<<CW)) else $error("BAUD_TICK_COUNT must fit CW");
    assert (HALF_BAUD_TICK_COUNT < (1<<CW)) else $error("HALF_BAUD_TICK_COUNT must fit CW");
    assert (TDW <= 15) else $error("TDW must fit 4-bit bit_counter");
    assert (TDW > 0) else $error("TDW must be > 0");
  end

  // Reset behavior
  assert property (reset |-> (baud_counter==0 && bit_counter==0 &&
                              !baud_clock_rising_edge && !baud_clock_falling_edge &&
                              !all_bits_transmitted));

  // reset_counters clears counters synchronously
  assert property (disable iff (reset)
                   reset_counters |-> (baud_counter==0 && bit_counter==0));

  // Baud counter: range, increment, rollover
  assert property (disable iff (reset) baud_counter <= BAUD_TICK_COUNT);
  assert property (disable iff (reset)
                   !$past(reset_counters) && $past(baud_counter)!=BAUD_TICK_COUNT
                   |-> baud_counter == $past(baud_counter)+1);
  assert property (disable iff (reset)
                   !$past(reset_counters) && $past(baud_counter)==BAUD_TICK_COUNT
                   |-> baud_counter == 0);

  // Baud edge pulses: exact match and 1-cycle width
  assert property (baud_clock_rising_edge  == (baud_counter==BAUD_TICK_COUNT));
  assert property (baud_clock_falling_edge == (baud_counter==HALF_BAUD_TICK_COUNT));
  assert property (disable iff (reset) baud_clock_rising_edge  |-> ##1 !baud_clock_rising_edge);
  assert property (disable iff (reset) baud_clock_falling_edge |-> ##1 !baud_clock_falling_edge);

  // Bit counter: range, increment on baud tick, hold otherwise, rollover
  assert property (disable iff (reset) bit_counter <= TDW);
  assert property (disable iff (reset)
                   !$past(reset_counters) && ($past(bit_counter) < TDW) &&
                   ($past(baud_counter)==BAUD_TICK_COUNT)
                   |-> bit_counter == $past(bit_counter)+1);
  assert property (disable iff (reset)
                   !$past(reset_counters) && ($past(bit_counter) < TDW) &&
                   ($past(baud_counter)!=BAUD_TICK_COUNT)
                   |-> bit_counter == $past(bit_counter));
  assert property (disable iff (reset)
                   !$past(reset_counters) && $past(bit_counter)==TDW
                   |-> bit_counter == 0);

  // all_bits_transmitted: exact match and next-state effect
  assert property (all_bits_transmitted == (bit_counter==TDW));
  assert property (disable iff (reset) all_bits_transmitted |-> ##1 bit_counter==0);

  // Optional: simultaneous edge pulse only if parameters equal
  assert property (!(baud_clock_rising_edge && baud_clock_falling_edge) ||
                   (BAUD_TICK_COUNT==HALF_BAUD_TICK_COUNT));

  // Coverage
  cover property (disable iff (reset) baud_clock_falling_edge ##[1:$] baud_clock_rising_edge);
  cover property (disable iff (reset) (bit_counter==0) ##[1:$] all_bits_transmitted);
  cover property (disable iff (reset) reset_counters ##1 (baud_counter==0 && bit_counter==0));

endmodule

// Bind into DUT (connects to internal regs by name)
bind altera_up_rs232_counters
  altera_up_rs232_counters_sva #(
    .CW(CW),
    .BAUD_TICK_COUNT(BAUD_TICK_COUNT),
    .HALF_BAUD_TICK_COUNT(HALF_BAUD_TICK_COUNT),
    .TDW(TDW)
  ) u_altera_up_rs232_counters_sva (.*);