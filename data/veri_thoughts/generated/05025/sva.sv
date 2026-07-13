module adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] Y
);

    // DUT has no native clock or reset; clk is a formal sampling clock.

    // Y matches the RTL's 8-bit addition expression.
    check_output_matches_truncated_sum: assert property (
        @(posedge clk) Y == (A + B)
    );

    // Without 9-bit overflow, Y equals the exact mathematical sum.
    check_exact_sum_without_overflow: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) <= 9'd255)
        |-> (Y == (({1'b0, A} + {1'b0, B})[7:0]))
    );

    // With 9-bit overflow, Y keeps only the low 8 bits.
    check_low_byte_on_overflow: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) > 9'd255)
        |-> (Y == (({1'b0, A} + {1'b0, B})[7:0]))
    );

    // Overflow does not clamp Y to 8'hFF.
    check_no_clamp_on_overflow: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) > 9'd255)
        |-> (Y != 8'hFF)
    );

endmodule