module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic cout,
    input logic [3:0] sum,
    input logic [7:0] count,
    input logic [11:0] result
);

    // Count is zero whenever reset is asserted low.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 8'h00)
    );

    // Count increments by one on each enabled clock.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!reset)
        enable |=> (count == ($past(count) + 8'd1))
    );

    // Count holds its value when enable is low.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        !enable |=> (count == $past(count))
    );

    // Adder outputs match the implemented zero-extended 4-bit sum.
    check_adder_outputs_match_rtl: assert property (
        @(posedge clk) disable iff (!reset)
        {cout, sum} == {1'b0, (a + b + cin)}
    );

    // Carry-out remains low in the implemented adder logic.
    check_adder_cout_zero: assert property (
        @(posedge clk) disable iff (!reset)
        cout == 1'b0
    );

    // Result matches the implemented zero-extended 8-bit addition.
    check_result_matches_rtl: assert property (
        @(posedge clk) disable iff (!reset)
        result == {4'b0, ({4'b0, sum} + count)}
    );

    // Result upper nibble stays zero in the implemented logic.
    check_result_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (!reset)
        result[11:8] == 4'b0
    );

endmodule