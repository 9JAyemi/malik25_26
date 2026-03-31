module square_module_sva (
    input logic clk,
    input logic [3:0] num,
    input logic [7:0] square
);

    // No RTL clock or reset; clk is an external sampling clock for this combinational DUT.

    // Square must equal num multiplied by itself.
    check_square_matches_product: assert property (
        @(posedge clk) {8'b0, square} == ({4'b0, num} * {4'b0, num})
    );

    // Zero input must produce zero output.
    check_zero_input_maps_to_zero: assert property (
        @(posedge clk) (num == 4'd0) |-> (square == 8'd0)
    );

    // Maximum 4-bit input must produce 225.
    check_max_input_maps_to_225: assert property (
        @(posedge clk) (num == 4'd15) |-> (square == 8'd225)
    );

    // Square parity must match input parity.
    check_square_parity_matches_input: assert property (
        @(posedge clk) square[0] == num[0]
    );

    // Output must remain stable when the sampled input remains stable.
    check_square_stable_when_num_stable: assert property (
        @(posedge clk) (num == $past(num)) |-> (square == $past(square))
    );

    // Different sampled inputs must produce different sampled outputs.
    check_distinct_inputs_produce_distinct_squares: assert property (
        @(posedge clk) (num != $past(num)) |-> (square != $past(square))
    );

    // Output must stay within the valid range for squaring a 4-bit value.
    check_square_within_valid_range: assert property (
        @(posedge clk) square <= 8'd225
    );

endmodule