module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] shift_amt,
    input logic mode,
    input logic [3:0] out,
    input logic equal,
    input logic signed_larger,
    input logic signed_smaller,
    input logic [3:0] larger_num,
    input logic [3:0] smaller_num,
    input logic [3:0] shifted_num
);

    // equal matches bitwise equality of A and B.
    check_equal_flag: assert property (
        @(posedge clk) equal == (A == B)
    );

    // signed_larger matches the signed A > B comparison.
    check_signed_larger_flag: assert property (
        @(posedge clk) signed_larger == ($signed(A) > $signed(B))
    );

    // signed_smaller matches the signed A < B comparison.
    check_signed_smaller_flag: assert property (
        @(posedge clk) signed_smaller == ($signed(A) < $signed(B))
    );

    // signed_larger and signed_smaller cannot both be high.
    check_compare_flags_mutex: assert property (
        @(posedge clk) !(signed_larger && signed_smaller)
    );

    // larger_num selects A when signed_larger is true, else B.
    check_larger_num_select: assert property (
        @(posedge clk) larger_num == (signed_larger ? A : B)
    );

    // smaller_num selects A when signed_smaller is true, else B.
    check_smaller_num_select: assert property (
        @(posedge clk) smaller_num == (signed_smaller ? A : B)
    );

    // In mode 1, shifted_num uses logical right shift.
    check_shift_right_logical_mode: assert property (
        @(posedge clk) mode |-> (shifted_num == (larger_num >> shift_amt))
    );

    // In mode 0, shifted_num matches the RTL >>> expression.
    check_shift_right_arithmetic_mode: assert property (
        @(posedge clk) !mode |-> (shifted_num == (larger_num >>> shift_amt))
    );

    // When equal is high, out is driven to zero.
    check_out_zero_when_equal: assert property (
        @(posedge clk) equal |-> (out == 4'b0000)
    );

    // When signed_larger is high, out follows shifted_num.
    check_out_shifted_when_signed_larger: assert property (
        @(posedge clk) (!equal && signed_larger) |-> (out == shifted_num)
    );

    // Otherwise, out follows smaller_num.
    check_out_smaller_otherwise: assert property (
        @(posedge clk) (!equal && !signed_larger) |-> (out == smaller_num)
    );

endmodule