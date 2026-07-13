module barrel_shift_mag_comp_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] shift,
    input logic [2:0] comparison_result,
    input logic [3:0] final_output
);

    // No RTL reset; assertions are always enabled.

    // comparison_result only uses the three implemented encodings.
    check_comparison_result_legal: assert property (
        @(posedge clk) disable iff (1'b0)
        (comparison_result == 3'b001) || (comparison_result == 3'b010) || (comparison_result == 3'b100)
    );

    // Shift 00 compares unshifted a against b.
    check_compare_shift_00: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b00) |-> (comparison_result == ((a > b) ? 3'b001 : ((a < b) ? 3'b010 : 3'b100)))
    );

    // Shift 01 compares a left-shifted by 1 against b.
    check_compare_shift_01: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b01) |-> (comparison_result == (({a[2:0], 1'b0} > b) ? 3'b001 : (({a[2:0], 1'b0} < b) ? 3'b010 : 3'b100)))
    );

    // Shift 10 compares a right-shifted by 1 against b.
    check_compare_shift_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b10) |-> (comparison_result == (({1'b0, a[3:1]} > b) ? 3'b001 : (({1'b0, a[3:1]} < b) ? 3'b010 : 3'b100)))
    );

    // Shift 11 compares a left-shifted by 2 against b.
    check_compare_shift_11: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b11) |-> (comparison_result == (({a[1:0], 2'b00} > b) ? 3'b001 : (({a[1:0], 2'b00} < b) ? 3'b010 : 3'b100)))
    );

    // Shift 00 drives final_output from the implemented compare/select logic.
    check_output_shift_00: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b00) |-> (final_output == ((a > b) ? a : ((a < b) ? b : (a | b))))
    );

    // Shift 01 drives final_output from the implemented compare/select logic.
    check_output_shift_01: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b01) |-> (final_output == (({a[2:0], 1'b0} > b) ? {a[2:0], 1'b0} : (({a[2:0], 1'b0} < b) ? b : ({a[2:0], 1'b0} | b))))
    );

    // Shift 10 drives final_output from the implemented compare/select logic.
    check_output_shift_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b10) |-> (final_output == (({1'b0, a[3:1]} > b) ? {1'b0, a[3:1]} : (({1'b0, a[3:1]} < b) ? b : ({1'b0, a[3:1]} | b))))
    );

    // Shift 11 drives final_output from the implemented compare/select logic.
    check_output_shift_11: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift == 2'b11) |-> (final_output == (({a[1:0], 2'b00} > b) ? {a[1:0], 2'b00} : (({a[1:0], 2'b00} < b) ? b : ({a[1:0], 2'b00} | b))))
    );

endmodule