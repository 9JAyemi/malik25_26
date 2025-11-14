// SVA for POR. Bind this file to the POR module.
// Focus: correct reset stretch, no glitches, counter behavior, and coverage.

module por_sva
  #(parameter int rst_time = 10)
  (
    input  logic       clk,
    input  logic       pwr,
    input  logic       rst,
    input  logic [3:0] rst_count,
    input  logic       pwr_prev
  );

  default clocking cb @(posedge clk); endclocking

  // Parameter fits counter width
  localparam int RSTCNT_MAX = (1<<$bits(rst_count)) - 1;
  ap_param_fit: assert property (rst_time <= RSTCNT_MAX);

  // pwr_prev must track previous pwr
  ap_pwr_prev: assert property (pwr_prev == $past(pwr,1,1'b0));

  // On power rise, reset must assert immediately
  ap_rst_on_pwr_rise: assert property ($rose(pwr) |-> rst);

  // No early deassert: hold reset for at least rst_time cycles
  ap_hold_min: assert property ($rose(pwr) |-> rst throughout (1'b1[*rst_time]));

  // Exact deassert: drop exactly rst_time cycles after rise (catches off-by-one)
  ap_drop_exact: assert property ($rose(pwr) |-> ##rst_time !rst);

  // Once deasserted, stay low until next power rising edge
  ap_stay_low_until_next_rise: assert property ((!rst && $past(rst)) |-> (!rst until $rose(pwr)));

  // Reset can only rise due to power rising edge
  ap_rst_rise_only_on_pwr_rise: assert property ($rose(rst) |-> $rose(pwr));

  // Counter behavior
  ap_cnt_zero_on_start: assert property ($rose(pwr) |-> rst_count == 0);
  ap_cnt_inc_while_asserting: assert property (rst && !$rose(pwr) && (rst_count < rst_time) |-> rst_count == $past(rst_count)+1);
  ap_cnt_stable_when_rst0: assert property (!rst |-> rst_count == $past(rst_count));
  ap_deassert_implies_cnt_reached: assert property ((!rst && $past(rst)) |-> $past(rst_count) >= rst_time);

  // Coverage
  cv_pwr_rise:                    cover property ($rose(pwr));
  cv_spec_duration:               cover property ($rose(pwr) and (rst throughout (1'b1[*rst_time])) ##rst_time !rst);
  cv_impl_off_by_one_duration:    cover property ($rose(pwr) and (rst throughout (1'b1[* (rst_time+1)])) ##(rst_time+1) !rst);

endmodule

// Bind into all POR instances; connects to internals by name.
bind POR por_sva #(.rst_time(rst_time)) por_sva_i (.*);