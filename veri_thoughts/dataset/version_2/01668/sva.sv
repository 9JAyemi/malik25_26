module odd_parity_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    ///// Functional equivalence /////
    // out must equal a ^ b ^ c (odd parity of the three inputs).
    check_parity_xor: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            out == (a ^ b ^ c)
    );

    ///// Truth table checks /////
    // 0 ones: out must be 0.
    check_zero_ones: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (!a && !b && !c) |-> (out == 1'b0)
    );
    // 1 one (a=1): out must be 1.
    check_one_hot_a: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (a && !b && !c) |-> (out == 1'b1)
    );
    // 1 one (b=1): out must be 1.
    check_one_hot_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (!a && b && !c) |-> (out == 1'b1)
    );
    // 1 one (c=1): out must be 1.
    check_one_hot_c: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (!a && !b && c) |-> (out == 1'b1)
    );
    // 2 ones (a&b): out must be 0.
    check_two_ones_ab: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (a && b && !c) |-> (out == 1'b0)
    );
    // 2 ones (a&c): out must be 0.
    check_two_ones_ac: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (a && !b && c) |-> (out == 1'b0)
    );
    // 2 ones (b&c): out must be 0.
    check_two_ones_bc: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (!a && b && c) |-> (out == 1'b0)
    );
    // 3 ones: out must be 1.
    check_three_ones: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
            (a && b && c) |-> (out == 1'b1)
    );

endmodule