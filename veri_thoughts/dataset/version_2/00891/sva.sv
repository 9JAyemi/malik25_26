module Vector_sva (
    input logic clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [1:0] c
);
    ///// Functional correctness /////
    // Output equals bitwise AND of inputs.
    check_and_functionality: assert property (
        @(posedge clk) c === (a & b)
    );
    // Commutativity of AND reflected at output.
    check_commutativity: assert property (
        @(posedge clk) c === (b & a)
    );

    ///// Bit-level correctness /////
    // Bit 0 equals a[0] AND b[0].
    check_bit0: assert property (
        @(posedge clk) c[0] === (a[0] & b[0])
    );
    // Bit 1 equals a[1] AND b[1].
    check_bit1: assert property (
        @(posedge clk) c[1] === (a[1] & b[1])
    );

    ///// Identity and annihilator properties /////
    // When a is all ones, c mirrors b.
    check_identity_a_all_ones: assert property (
        @(posedge clk) (a == 2'b11) |-> (c === b)
    );
    // When b is all ones, c mirrors a.
    check_identity_b_all_ones: assert property (
        @(posedge clk) (b == 2'b11) |-> (c === a)
    );
    // When a is all zeros, c is zero.
    check_annihilator_a_all_zeros: assert property (
        @(posedge clk) (a == 2'b00) |-> (c === 2'b00)
    );
    // When b is all zeros, c is zero.
    check_annihilator_b_all_zeros: assert property (
        @(posedge clk) (b == 2'b00) |-> (c === 2'b00)
    );

    ///// Subset properties /////
    // Output ones are a subset of a's ones.
    check_output_subset_of_a: assert property (
        @(posedge clk) ((c & ~a) === 2'b00)
    );
    // Output ones are a subset of b's ones.
    check_output_subset_of_b: assert property (
        @(posedge clk) ((c & ~b) === 2'b00)
    );
endmodule