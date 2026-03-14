module twos_complement_sva (
    input logic clk,               // sampling clock for assertions (DUT has no clock/reset)
    input logic [3:0] binary,
    input logic [3:0] twos_comp
);

    // twos_comp implements ~binary + 1
    check_twos_comp_definition: assert property (
        @(posedge clk) twos_comp == (~binary + 4'b0001)
    );

    // binary + twos_comp wraps to 0 (mod 16)
    check_zero_sum_mod16: assert property (
        @(posedge clk) (binary + twos_comp) == 4'b0000
    );

    // Two's complement is an involution: t(t(x)) == x
    check_double_complement_returns_input: assert property (
        @(posedge clk) (~twos_comp + 4'b0001) == binary
    );

    // LSB is preserved by two's complement
    check_lsb_preserved: assert property (
        @(posedge clk) twos_comp[0] == binary[0]
    );

    // Zero maps to zero
    check_zero_input_gives_zero_output: assert property (
        @(posedge clk) (binary == 4'b0000) |-> (twos_comp == 4'b0000)
    );

    // Only zero maps to zero
    check_only_zero_maps_to_zero: assert property (
        @(posedge clk) (twos_comp == 4'b0000) |-> (binary == 4'b0000)
    );

    // Minimum 4-bit signed value (1000) maps to itself
    check_min_int_fixed_point: assert property (
        @(posedge clk) (binary == 4'b1000) |-> (twos_comp == 4'b1000)
    );

    // No other value is a fixed point
    check_non_fixed_point_for_others: assert property (
        @(posedge clk) ((binary != 4'b0000) && (binary != 4'b1000)) |-> (twos_comp != binary)
    );

    // Subtracting 1 from result yields bitwise NOT of input
    check_subtract_one_equals_not_input: assert property (
        @(posedge clk) (twos_comp - 4'b0001) == ~binary
    );

    // Bitwise NOT of result equals input minus 1
    check_not_result_equals_input_minus_one: assert property (
        @(posedge clk) ~twos_comp == (binary - 4'b0001)
    );

endmodule