module bcd_to_binary_assertions (
    input logic        clk,
    input logic [3:0]  bcd0,
    input logic [3:0]  bcd1,
    input logic [3:0]  bcd2,
    input logic [3:0]  bcd3,
    input logic [3:0]  bin
);

    function automatic [3:0] expected_bin (
        input logic [3:0] d0,
        input logic [3:0] d1,
        input logic [3:0] d2,
        input logic [3:0] d3
    );
        begin
            expected_bin = (d3 * 1000) + (d2 * 100) + (d1 * 10) + d0;
        end
    endfunction

    // bin matches the RTL weighted sum with 4-bit truncation.
    check_weighted_sum: assert property (
        @(posedge clk) bin == expected_bin(bcd0, bcd1, bcd2, bcd3)
    );

    // All-zero inputs produce a zero output.
    check_zero_input_zero_output: assert property (
        @(posedge clk) (bcd0 == 4'd0 && bcd1 == 4'd0 && bcd2 == 4'd0 && bcd3 == 4'd0) |-> (bin == 4'd0)
    );

    // With only the ones digit active, bin equals bcd0.
    check_ones_digit_passthrough: assert property (
        @(posedge clk) (bcd1 == 4'd0 && bcd2 == 4'd0 && bcd3 == 4'd0) |-> (bin == bcd0)
    );

    // With only the tens digit active, bin matches the truncated tens contribution.
    check_tens_digit_only: assert property (
        @(posedge clk) (bcd0 == 4'd0 && bcd2 == 4'd0 && bcd3 == 4'd0) |-> (bin == expected_bin(4'd0, bcd1, 4'd0, 4'd0))
    );

    // With only the hundreds digit active, bin matches the truncated hundreds contribution.
    check_hundreds_digit_only: assert property (
        @(posedge clk) (bcd0 == 4'd0 && bcd1 == 4'd0 && bcd3 == 4'd0) |-> (bin == expected_bin(4'd0, 4'd0, bcd2, 4'd0))
    );

    // With only the thousands digit active, bin matches the truncated thousands contribution.
    check_thousands_digit_only: assert property (
        @(posedge clk) (bcd0 == 4'd0 && bcd1 == 4'd0 && bcd2 == 4'd0) |-> (bin == expected_bin(4'd0, 4'd0, 4'd0, bcd3))
    );

    // The output LSB is determined solely by the ones digit.
    check_lsb_depends_on_bcd0_only: assert property (
        @(posedge clk) bin[0] == bcd0[0]
    );

    // Stable inputs keep the combinational output stable across samples.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({bcd3, bcd2, bcd1, bcd0}) |-> $stable(bin)
    );

endmodule