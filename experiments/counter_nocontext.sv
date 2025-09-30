// SystemVerilog Assertions for module counter
// This file "binds" properties to the DUT without modifying the original source.
// Supports conditional compilation macros: check1 (reset behavior), check2 (hold branch removed), check3 (reverse count direction)
// Place in compile list after counter.sv or use +incdir+.

`ifndef COUNTER_ASSERTIONS_SV
`define COUNTER_ASSERTIONS_SV

// If your simulator requires explicit timeunit/timeprecision
//`timescale 1ns/1ps
// or
// timeunit 1ns; timeprecision 1ps;

module counter_sva #(parameter WIDTH = 8) (input logic clk, rst_, ld_cnt_, updn_cnt, count_enb,
                                          input logic [WIDTH-1:0] data_in,
                                          input logic [WIDTH-1:0] data_out);

  // ---------------------------------------------
  // Helper signals
  // ---------------------------------------------
  logic [WIDTH-1:0] prev; // previous value for some relational checks
  always_ff @(posedge clk or negedge rst_) begin
    if (!rst_) prev <= '0; else prev <= data_out; // previous cycle value
  end

  // Macro-based description of direction
  // With check3 defined the case swaps add/sub.
`ifdef check3
  localparam string COUNT_MODE_DESC = "check3: updn_cnt=1 => decrement";
`else
  localparam string COUNT_MODE_DESC = "default: updn_cnt=1 => increment";
`endif

  // ---------------------------------------------
  // Property: Asynchronous Reset (if check1 not defined the DUT drives 0 on reset)
  // ---------------------------------------------
  // When rst_ asserted low, after the same cycle (async) data_out must be 0 (only if design code present)
`ifndef check1
  property p_reset_forces_zero;
    (!rst_) |-> (data_out == '0);
  endproperty
  a_reset_forces_zero: assert property(p_reset_forces_zero)
    else $error("RESET: data_out not zero while rst_ low");
`endif

  // ---------------------------------------------
  // Property: Load takes precedence over hold/count (active low ld_cnt_)
  // On a rising clock edge, if ld_cnt_ is 0 and rst_ is high, data_out should equal data_in next cycle.
  // Because design loads in same cycle (non-blocking), we check sampled at posedge.
  property p_load_priority;
    @(posedge clk) disable iff(!rst_) (!ld_cnt_) |-> (data_out == data_in);
  endproperty
  a_load_priority: assert property(p_load_priority)
    else $error("LOAD: data_out != data_in when ld_cnt_ active");

  // ---------------------------------------------
  // Property: Hold behavior (only if hold branch present i.e. check2 not defined)
  // If count_enb==0 and ld_cnt_==1 then value must hold & not change.
`ifndef check2
  property p_hold_when_disabled;
    @(posedge clk) disable iff(!rst_) (ld_cnt_ && !count_enb) |-> $stable(data_out);
  endproperty
  a_hold_when_disabled: assert property(p_hold_when_disabled)
    else $error("HOLD: data_out changed while count_enb=0");
`endif

  // ---------------------------------------------
  // Property: Counting direction
  // When counting (ld_cnt_==1, count_enb==1) value changes by +1 or -1 according to updn_cnt & macros.
  // We also exclude the load condition.
  // Use two properties for clarity.

`ifdef check3
  // Inverted direction variant
  property p_count_down_when_updn_is_1;
    @(posedge clk) disable iff(!rst_) (ld_cnt_ && count_enb && updn_cnt) |-> (data_out == prev - 1);
  endproperty
  a_count_down_when_updn_is_1: assert property(p_count_down_when_updn_is_1)
    else $error("COUNT(check3): Expected decrement when updn_cnt=1");

  property p_count_up_when_updn_is_0;
    @(posedge clk) disable iff(!rst_) (ld_cnt_ && count_enb && !updn_cnt) |-> (data_out == prev + 1);
  endproperty
  a_count_up_when_updn_is_0: assert property(p_count_up_when_updn_is_0)
    else $error("COUNT(check3): Expected increment when updn_cnt=0");
`else
  // Default direction variant
  property p_count_up_when_updn_is_1;
    @(posedge clk) disable iff(!rst_) (ld_cnt_ && count_enb && updn_cnt) |-> (data_out == prev + 1);
  endproperty
  a_count_up_when_updn_is_1: assert property(p_count_up_when_updn_is_1)
    else $error("COUNT: Expected increment when updn_cnt=1");

  property p_count_down_when_updn_is_0;
    @(posedge clk) disable iff(!rst_) (ld_cnt_ && count_enb && !updn_cnt) |-> (data_out == prev - 1);
  endproperty
  a_count_down_when_updn_is_0: assert property(p_count_down_when_updn_is_0)
    else $error("COUNT: Expected decrement when updn_cnt=0");
`endif

  // ---------------------------------------------
  // Property: No spurious changes (only transitions allowed: load, hold (no change), count +/-1)
  // Skip during reset. If value changes by something other than +/-1 on a count cycle or arbitrary change on load cycle -> error.
  property p_only_valid_transitions;
    @(posedge clk) disable iff(!rst_)
      (ld_cnt_ && count_enb && (data_out != prev)) |-> ((data_out == prev + 1) || (data_out == prev - 1));
  endproperty
  a_only_valid_transitions: assert property(p_only_valid_transitions)
    else $error("TRANSITION: Invalid delta (not +/-1) during count");

  // ---------------------------------------------
  // Property: Load overrides counting (i.e., if ld_cnt_==0 we should not apply +/-1 rule)
  property p_load_not_increment;
    @(posedge clk) disable iff(!rst_)
      (!ld_cnt_) |-> (data_out == data_in);
  endproperty
  a_load_not_increment: assert property(p_load_not_increment)
    else $error("LOAD: Unexpected modification during load");

  // ---------------------------------------------
  // Optional wrap-around coverage (show that we hit overflow and underflow edges)
  // Hit all zeros and all ones, and transitions through them while counting.
  covergroup cg_counter @(posedge clk);
    coverpoint data_out {
      bins zero = {0};
      bins max  = { {WIDTH{1'b1}} };
    }
  endgroup
  cg_counter cov_inst = new();

  // Edge transition coverage
  property p_wrap_from_max_to_zero;
    @(posedge clk) disable iff(!rst_)
      (ld_cnt_ && count_enb && prev == {WIDTH{1'b1}} && (
`ifdef check3
        // direction reversed
        !updn_cnt // increment direction under check3
`else
        updn_cnt  // increment direction default
`endif
      )) |-> (data_out == '0);
  endproperty
  c_wrap_from_max_to_zero: cover property(p_wrap_from_max_to_zero);

  property p_wrap_from_zero_to_max;
    @(posedge clk) disable iff(!rst_)
      (ld_cnt_ && count_enb && prev == '0 && (
`ifdef check3
        updn_cnt // decrement direction under check3
`else
        !updn_cnt // decrement direction default
`endif
      )) |-> (data_out == {WIDTH{1'b1}});
  endproperty
  c_wrap_from_zero_to_max: cover property(p_wrap_from_zero_to_max);

endmodule

// Bind to all instances of counter (adjust instance path as needed if hierarchical)
bind counter counter_sva #(8) counter_sva_i (.*);

`endif // COUNTER_ASSERTIONS_SV
