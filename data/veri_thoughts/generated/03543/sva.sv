module four_bit_comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic out
);

    // out must be high when A is greater than B.
    check_out_high_on_greater: assert property (
        @(posedge clk) (A > B) |-> (out == 1'b1)
    );

    // out must be low when A is less than B.
    check_out_low_on_less: assert property (
        @(posedge clk) (A < B) |-> (out == 1'b0)
    );

    // out must be low when A equals B.
    check_out_low_on_equal: assert property (
        @(posedge clk) (A == B) |-> (out == 1'b0)
    );

    // out can only be high for a greater-than comparison.
    check_out_high_implies_greater: assert property (
        @(posedge clk) (out == 1'b1) |-> (A > B)
    );

endmodule