// SVA for Registro_Universal
// Focused, high-quality checks and coverage. Bind-only; no DUT edits.

module Registro_Universal_sva
  #(parameter N = 8)
  (
    input logic                 hold,
    input logic [N-1:0]         in_rtc_dato,
    input logic [N-1:0]         in_count_dato,
    input logic                 clk,
    input logic                 reset,
    input logic                 chip_select,
    input logic [N-1:0]         out_dato
  );

  // Mature after first active negedge post-reset to make $past safe
  logic init_done;
  always @(negedge clk or posedge reset)
    if (reset) init_done <= 1'b0;
    else       init_done <= 1'b1;

  // Asynchronous reset behavior
  assert property (@(posedge reset) out_dato == '0)
    else $error("out_dato not cleared immediately on reset");

  assert property (@(negedge clk) reset |-> out_dato == '0)
    else $error("out_dato not held at zero during reset");

  // Functional updates on negedge clk
  assert property (@(negedge clk) disable iff (!init_done)
                   hold |=> out_dato == $past(out_dato))
    else $error("Hold failed to retain out_dato");

  assert property (@(negedge clk) disable iff (!init_done)
                   (!hold && !chip_select) |=> out_dato == $past(in_rtc_dato))
    else $error("Select=0 path did not capture in_rtc_dato");

  assert property (@(negedge clk) disable iff (!init_done)
                   (!hold &&  chip_select) |=> out_dato == $past(in_count_dato))
    else $error("Select=1 path did not capture in_count_dato");

  // No unintended updates on posedge clk
  assert property (@(posedge clk) disable iff (!init_done) $stable(out_dato))
    else $error("out_dato changed on posedge clk");

  // X/Z hygiene when used
  assert property (@(negedge clk) disable iff (!init_done) !$isunknown({hold,chip_select}))
    else $error("hold or chip_select is X/Z");

  assert property (@(negedge clk) disable iff (!init_done)
                   (!hold && !chip_select) |-> !$isunknown(in_rtc_dato))
    else $error("in_rtc_dato is X/Z when selected");

  assert property (@(negedge clk) disable iff (!init_done)
                   (!hold &&  chip_select) |-> !$isunknown(in_count_dato))
    else $error("in_count_dato is X/Z when selected");

  assert property (@(negedge clk) disable iff (!init_done) !$isunknown(out_dato))
    else $error("out_dato is X/Z");

  // Minimal, meaningful coverage
  cover property (@(posedge reset) 1);                 // reset seen
  cover property (@(negedge clk) $fell(reset));        // reset release seen

  cover property (@(negedge clk) disable iff (!init_done)
                  (!hold && !chip_select) ##1 out_dato == $past(in_rtc_dato)); // rtc path
  cover property (@(negedge clk) disable iff (!init_done)
                  (!hold &&  chip_select) ##1 out_dato == $past(in_count_dato)); // count path

  cover property (@(negedge clk) disable iff (!init_done) hold[*2]); // multi-cycle hold
  cover property (@(negedge clk) disable iff (!init_done)
                  (!hold && !chip_select) ##1 hold ##1 (!hold && chip_select)); // both paths with hold between

endmodule

// Bind into DUT
bind Registro_Universal
  Registro_Universal_sva #(.N(N)) u_registro_universal_sva (
    .hold(hold),
    .in_rtc_dato(in_rtc_dato),
    .in_count_dato(in_count_dato),
    .clk(clk),
    .reset(reset),
    .chip_select(chip_select),
    .out_dato(out_dato)
  );