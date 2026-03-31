module top_module_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic clk,
    input logic [31:0] result
);

    // Result must match the RTL's muxed adder selection.
    check_result_mux: assert property (
        @(posedge clk) result == (sub ? {16'h0000, a[31:16]} : {16'h0000, a[15:0]})
    );

    // In add mode, result must equal the low 16 bits of a.
    check_add_mode_result: assert property (
        @(posedge clk) !sub |-> (result == {16'h0000, a[15:0]})
    );

    // In subtract mode, result must equal the upper 16 bits of a.
    check_sub_mode_result: assert property (
        @(posedge clk) sub |-> (result == {16'h0000, a[31:16]})
    );

    // In add mode, the upper 16 bits of result must be zero.
    check_add_mode_upper_zero: assert property (
        @(posedge clk) !sub |-> (result[31:16] == 16'h0000)
    );

    // In subtract mode, the lower 16 bits of result must be zero.
    check_sub_mode_lower_zero: assert property (
        @(posedge clk) sub |-> (result[15:0] == 16'h0000)
    );

    // If a and sub are stable, result must remain stable.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a, sub}) |-> $stable(result)
    );

endmodule