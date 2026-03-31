module debouncer_sva (
  input logic clk,
  input logic in,
  input logic out,
  input logic [1:0] state,
  input logic [31:0] debounce_count
);
  // Clock: clk (posedge). No reset in RTL.
  // Sequential FSM with counter; internal: state, debounce_count.

  // Mirror DUT parameters for checks
  parameter int unsigned clk_freq = 100000;
  parameter int unsigned debounce_time = 10;
  localparam logic [31:0] LOAD_VALUE = (debounce_time * clk_freq) / 1000;

  // State encodings from RTL
  localparam logic [1:0] STABLE   = 2'b00;
  localparam logic [1:0] UNSTABLE = 2'b01;
  localparam logic [1:0] DEBOUNCE = 2'b10;

  // From STABLE with input/output mismatch, go to UNSTABLE and load counter.
  stable_to_unstable_on_mismatch_loads_count: assert property (
    @(posedge clk) (state == STABLE) && (in != out)
      |=> (state == UNSTABLE) && (debounce_count == LOAD_VALUE)
  );

  // From STABLE with input/output match, remain in STABLE and hold outputs/counter.
  stable_holds_when_inputs_match: assert property (
    @(posedge clk) (state == STABLE) && (in == out)
      |=> (state == STABLE) && $stable(out) && $stable(debounce_count)
  );

  // In UNSTABLE with counter > 0, stay UNSTABLE, decrement counter by 1, and hold output.
  unstable_decrements_and_holds_out: assert property (
    @(posedge clk) (state == UNSTABLE) && (debounce_count > 0)
      |=> (state == UNSTABLE) && (debounce_count == $past(debounce_count) - 32'd1) && $stable(out)
  );

  // In UNSTABLE with counter == 0, go to DEBOUNCE and update output to previous input.
  unstable_to_debounce_updates_output: assert property (
    @(posedge clk) (state == UNSTABLE) && (debounce_count == 0)
      |=> (state == DEBOUNCE) && (out == $past(in))
  );

  // In DEBOUNCE with input/output match, go to STABLE and hold output/counter.
  debounce_to_stable_on_match: assert property (
    @(posedge clk) (state == DEBOUNCE) && (in == out)
      |=> (state == STABLE) && $stable(out) && $stable(debounce_count)
  );

  // In DEBOUNCE with input/output mismatch, go to UNSTABLE and load counter.
  debounce_to_unstable_on_mismatch_loads_count: assert property (
    @(posedge clk) (state == DEBOUNCE) && (in != out)
      |=> (state == UNSTABLE) && (debounce_count == LOAD_VALUE)
  );

  // Output may change only when previously in UNSTABLE with counter == 0 and now in DEBOUNCE.
  out_changes_only_on_unstable_zero: assert property (
    @(posedge clk) $changed(out)
      |-> ($past(state) == UNSTABLE) && ($past(debounce_count) == 0) && (state == DEBOUNCE)
  );

  // While in STABLE, output holds its value to the next cycle.
  out_stable_in_STABLE: assert property (
    @(posedge clk) (state == STABLE) |=> $stable(out)
  );

  // While in DEBOUNCE, output holds its value to the next cycle.
  out_stable_in_DEBOUNCE: assert property (
    @(posedge clk) (state == DEBOUNCE) |=> $stable(out)
  );

  // If state is not one of the encoded values, all registers hold (no assignments in case default).
  non_enumerated_state_holds_all: assert property (
    @(posedge clk) !(state inside {STABLE, UNSTABLE, DEBOUNCE})
      |=> (state == $past(state)) && $stable(out) && $stable(debounce_count)
  );
endmodule