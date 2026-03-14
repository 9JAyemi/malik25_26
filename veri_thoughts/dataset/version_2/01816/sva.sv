module top_module_sva (
    input logic clk,
    input logic reset,       // Counter treats reset as active-low (reset==0 asserted)
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always,
    input logic [3:0] q_counter,
    input logic [3:0] mux_out,
    input logic [3:0] adder_out
);
    // Counter loads 8 on the cycle after reset is low.
    check_counter_load_8_next_on_reset_low: assert property (
        @(posedge clk) (reset == 1'b0) |=> (q_counter == 4'b1000)
    );

    // If reset was low last cycle, counter must read 8 this cycle.
    check_counter_is_8_after_reset_low: assert property (
        @(posedge clk) ($past(reset) == 1'b0) |-> (q_counter == 4'b1000)
    );

    // When both selects are HIGH, mux must drive constant 0xF.
    check_mux_out_b_when_both_high: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (sel_b1 && sel_b2) |-> (mux_out == 4'hF)
    );

    // When not both HIGH, mux must pass through q_counter.
    check_mux_out_a_otherwise: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (!(sel_b1 && sel_b2)) |-> (mux_out == q_counter)
    );

    // Adder output equals q_counter + mux_out (mod 16).
    check_adder_sum_correct: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (adder_out == (q_counter + mux_out)[3:0])
    );

    // With both selects HIGH, adder sums q_counter + 0xF (mod 16).
    check_adder_sum_both_case: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (sel_b1 && sel_b2) |-> (adder_out == (q_counter + 4'hF)[3:0])
    );

    // With not both HIGH, adder sums q_counter + q_counter (mod 16).
    check_adder_sum_a_case: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (!(sel_b1 && sel_b2)) |-> (adder_out == (q_counter + q_counter)[3:0])
    );

    // out_always must be 1 one cycle after any clock edge.
    check_out_always_one_cycle_later_high: assert property (
        @(posedge clk) disable iff (reset == 1'b0) 1'b1 |-> ##1 (out_always == 1'b1)
    );

    // Once out_always is 1, it stays 1 on the next cycle.
    check_out_always_stable_high: assert property (
        @(posedge clk) disable iff (reset == 1'b0) out_always |-> ##1 out_always
    );

    // Combined path: adder equals q_counter + (mux selection) (mod 16).
    check_adder_conditional_sum_consistency: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            adder_out == (q_counter + ((sel_b1 && sel_b2) ? 4'hF : q_counter))[3:0]
    );
endmodule