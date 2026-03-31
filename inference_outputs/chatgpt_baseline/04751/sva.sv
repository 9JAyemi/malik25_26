module bitwise_and_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] result
);

    // Result matches the full bitwise AND of the inputs.
    check_result_vector_and: assert property (
        @(posedge clk) result === (a & b)
    );

    // Bit 0 of result matches a[0] & b[0].
    check_result_bit0_and: assert property (
        @(posedge clk) result[0] === (a[0] & b[0])
    );

    // Bit 1 of result matches a[1] & b[1].
    check_result_bit1_and: assert property (
        @(posedge clk) result[1] === (a[1] & b[1])
    );

    // Bit 2 of result matches a[2] & b[2].
    check_result_bit2_and: assert property (
        @(posedge clk) result[2] === (a[2] & b[2])
    );

    // Bit 3 of result matches a[3] & b[3].
    check_result_bit3_and: assert property (
        @(posedge clk) result[3] === (a[3] & b[3])
    );

    // Zero on a forces a zero result.
    check_zero_when_a_zero: assert property (
        @(posedge clk) (a === 4'h0) |-> (result === 4'h0)
    );

    // Zero on b forces a zero result.
    check_zero_when_b_zero: assert property (
        @(posedge clk) (b === 4'h0) |-> (result === 4'h0)
    );

    // All ones on a passes b through to the result.
    check_passthrough_when_a_all_ones: assert property (
        @(posedge clk) (a === 4'hF) |-> (result === b)
    );

    // All ones on b passes a through to the result.
    check_passthrough_when_b_all_ones: assert property (
        @(posedge clk) (b === 4'hF) |-> (result === a)
    );

    // All ones on both inputs produces all ones on the result.
    check_all_ones_when_both_all_ones: assert property (
        @(posedge clk) ((a === 4'hF) && (b === 4'hF)) |-> (result === 4'hF)
    );

endmodule