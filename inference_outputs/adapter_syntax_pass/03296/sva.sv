module top_module_sva (
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

    // equal is the combinational equality of A and B.
    check_equal_definition: assert property (
        @($global_clock) equal == (A == B)
    );

    // signed_larger is the combinational signed comparison of A and B.
    check_signed_larger_definition: assert property (
        @($global_clock) signed_larger == ($signed(A) > $signed(B))
    );

    // signed_smaller is the combinational signed comparison of A and B.
    check_signed_smaller_definition: assert property (
        @($global_clock) signed_smaller == ($signed(A) < $signed(B))
    );

    // larger_num selects A when signed_larger is true.
    check_larger_num_select_a: assert property (
        @($global_clock) signed_larger |-> (larger_num == A)
    );

    // larger_num selects B when signed_larger is false.
    check_larger_num_select_b: assert property (
        @($global_clock) !signed_larger |-> (larger_num == B)
    );

    // smaller_num selects A when signed_smaller is true.
    check_smaller_num_select_a: assert property (
        @($global_clock) signed_smaller |-> (smaller_num == A)
    );

    // smaller_num selects B when signed_smaller is false.
    check_smaller_num_select_b: assert property (
        @($global_clock) !signed_smaller |-> (smaller_num == B)
    );

    // shifted_num is the combinational right shift of larger_num.
    check_shifted_num_definition: assert property (
        @($global_clock) shifted_num == (mode ? (larger_num >> shift_amt) : (larger_num >>> shift_amt))
    );

    // out is zero when the inputs are equal.
    check_out_zero_when_equal: assert property (
        @($global_clock) equal |-> (out == 4'h0)
    );

    // out is the shifted larger number when A is signed larger than B.
    check_out_shifted_a_when_signed_larger: assert property (
        @($global_clock) (signed_larger && !equal) |-> (out == shifted_num)
    );

    // out is B when A is signed smaller than B.
    check_out_b_when_signed_smaller: assert property (
        @($global_clock) (signed_smaller && !equal) |-> (out == B)
    );

endmodule