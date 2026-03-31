module parity_check_sva (
    input logic [7:0] data,
    input logic       parity_error
);

    // parity_error must equal the RTL's comparison of the XOR result to 1.
    check_parity_error_matches_rtl: assert property (
        @($global_clock) parity_error == ((^data) == 1'b1)
    );

    // A zero XOR result must drive parity_error low.
    check_zero_xor_clears_error: assert property (
        @($global_clock) ((^data) == 1'b0) |-> (parity_error == 1'b0)
    );

    // A one XOR result must drive parity_error high.
    check_one_xor_sets_error: assert property (
        @($global_clock) ((^data) == 1'b1) |-> (parity_error == 1'b1)
    );

    // All-zero input must produce a zero XOR result and clear the error.
    check_all_zero_input_clears_error: assert property (
        @($global_clock) (data == 8'h00) |-> ((^data) == 1'b0 && (parity_error == 1'b0))
    );

    // All-one input must produce a zero XOR result and clear the error.
    check_all_one_input_clears_error: assert property (
        @($global_clock) (data == 8'hFF) |-> ((^data) == 1'b0 && (parity_error == 1'b0))
    );

    // Any input with a zero parity bit must not assert parity_error.
    check_even_parity_clears_error: assert property (
        @($global_clock) ((^data) == 1'b0) |-> (parity_error == 1'b0)
    );

    // Any input with a one parity bit must assert parity_error.
    check_odd_parity_sets_error: assert property (
        @($global_clock) ((^data) == 1'b1) |-> (parity_error == 1'b1)
    );

endmodule