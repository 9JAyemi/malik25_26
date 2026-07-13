module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic [31:0] in,
    input logic [31:0] out
);
    // Clock: clk; Reset: reset (active-high). Mixed: add_sub combinational; transition_detector sequential; top combines both.

    ///// Reset behavior /////
    // During reset, transition_detector output is 0 => out = base + in.
    check_out_plus_during_reset: assert property (
        @(posedge clk) reset |-> (out == ((sub ? b : (a + b)) + in))
    );

    ///// Edge-driven selection of add/sub on in[0] rising /////
    // On in[0] rising edge with sub==0, out = (a+b) - in that cycle.
    check_rise_sub0_minus: assert property (
        @(posedge clk) disable iff (reset) ($rose(in[0]) && (sub == 1'b0)) |-> (out == ((a + b) - in))
    );
    // On in[0] rising edge with sub==1, out = b - in that cycle.
    check_rise_sub1_minus: assert property (
        @(posedge clk) disable iff (reset) ($rose(in[0]) && (sub == 1'b1)) |-> (out == (b - in))
    );

    ///// Edge-driven selection of add/sub on in[0] falling /////
    // On in[0] falling edge with sub==0, out = (a+b) + in that cycle.
    check_fall_sub0_plus: assert property (
        @(posedge clk) disable iff (reset) ($fell(in[0]) && (sub == 1'b0)) |-> (out == ((a + b) + in))
    );
    // On in[0] falling edge with sub==1, out = b + in that cycle.
    check_fall_sub1_plus: assert property (
        @(posedge clk) disable iff (reset) ($fell(in[0]) && (sub == 1'b1)) |-> (out == (b + in))
    );

    ///// One-cycle hold after edge when in[0] remains level /////
    // After a rise, if in[0] stays high next cycle, out remains base - in.
    check_hold_after_rise_one_cycle: assert property (
        @(posedge clk) disable iff (reset) $rose(in[0]) ##1 (in[0] == 1'b1) |-> (out == ((sub ? b : (a + b)) - in))
    );
    // After a fall, if in[0] stays low next cycle, out remains base + in.
    check_hold_after_fall_one_cycle: assert property (
        @(posedge clk) disable iff (reset) $fell(in[0]) ##1 (in[0] == 1'b0) |-> (out == ((sub ? b : (a + b)) + in))
    );

    ///// Post-reset first active clock behavior /////
    // Immediately after reset deasserts, if in[0]==1, out = base - in.
    check_post_reset_deassert_high_lsb: assert property (
        @(posedge clk) $fell(reset) && (in[0] == 1'b1) |-> (out == ((sub ? b : (a + b)) - in))
    );
    // Immediately after reset deasserts, if in[0]==0, out = base + in.
    check_post_reset_deassert_low_lsb: assert property (
        @(posedge clk) $fell(reset) && (in[0] == 1'b0) |-> (out == ((sub ? b : (a + b)) + in))
    );

    ///// Arithmetic consistency at transition edges /////
    // On in[0] rising edge, out + in equals base.
    check_rise_arith_consistency: assert property (
        @(posedge clk) disable iff (reset) $rose(in[0]) |-> ((out + in) == (sub ? b : (a + b)))
    );
    // On in[0] falling edge, out - in equals base.
    check_fall_arith_consistency: assert property (
        @(posedge clk) disable iff (reset) $fell(in[0]) |-> ((out - in) == (sub ? b : (a + b)))
    );

endmodule