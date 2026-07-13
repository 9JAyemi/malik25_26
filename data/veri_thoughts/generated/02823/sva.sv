module full_adder_sva (
    input logic a,
    input logic b,
    input logic c_in,
    input logic sum,
    input logic c_out
);
    // sum equals a ^ b ^ c_in
    check_sum_def: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        sum == (a ^ b ^ c_in)
    );

    // c_out equals (a & b) | (c_in & (a ^ b))
    check_c_out_def: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        c_out == ((a & b) | (c_in & (a ^ b)))
    );

    // c_out equals majority form (a&b)|(a&c_in)|(b&c_in)
    check_c_out_majority_equiv: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        c_out == ((a & b) | (a & c_in) | (b & c_in))
    );

    // When c_in is 0, sum is a ^ b
    check_sum_when_cin0: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (c_in == 1'b0) |-> (sum == (a ^ b))
    );

    // When c_in is 1, sum is ~(a ^ b)
    check_sum_when_cin1: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (c_in == 1'b1) |-> (sum == ~(a ^ b))
    );

    // When c_in is 0, c_out is a & b
    check_c_out_when_cin0: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (c_in == 1'b0) |-> (c_out == (a & b))
    );

    // When c_in is 1, c_out is a | b
    check_c_out_when_cin1: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (c_in == 1'b1) |-> (c_out == (a | b))
    );

    // If a equals b, sum equals c_in
    check_sum_when_a_eq_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (a == b) |-> (sum == c_in)
    );

    // Exactly one input high -> sum=1, c_out=0
    check_onehot_behavior: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (( a & ~b & ~c_in) | (~a &  b & ~c_in) | (~a & ~b &  c_in)) |-> (sum == 1'b1 && c_out == 1'b0)
    );

    // Exactly two inputs high -> sum=0, c_out=1
    check_twohot_behavior: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        ((a & b & ~c_in) | (a & ~b & c_in) | (~a & b & c_in)) |-> (sum == 1'b0 && c_out == 1'b1)
    );

    // All inputs low -> sum=0, c_out=0
    check_all_zero_behavior: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c_in or negedge c_in)
        (~a & ~b & ~c_in) |-> (sum == 1'b0 && c_out == 1'b0)
    );
endmodule