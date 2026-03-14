module ones_counter_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [2:0] b
);
    ///// Direct implementation checks /////
    // b[2] equals ~(a3&a2&a1&a0).
    check_b2_definition: assert property (
        @(posedge CLK) b[2] == ~(a[3] & a[2] & a[1] & a[0])
    );
    // b[1] equals conjunction of negated 3-one minterms.
    check_b1_definition: assert property (
        @(posedge CLK) b[1] == ( ~(a[3] & a[2] & a[1] & ~a[0])
                               & ~(a[3] & a[2] & ~a[1] & a[0])
                               & ~(a[3] & ~a[2] & a[1] & a[0])
                               & ~(~a[3] & a[2] & a[1] & a[0]) )
    );
    // b[0] equals conjunction of negated 2-one minterms and negated 4-ones.
    check_b0_definition: assert property (
        @(posedge CLK) b[0] == ( ~(a[3] & a[2] & ~a[1] & ~a[0])
                               & ~(a[3] & ~a[2] & a[1] & ~a[0])
                               & ~(a[3] & ~a[2] & ~a[1] & a[0])
                               & ~(~a[3] & a[2] & a[1] & ~a[0])
                               & ~(~a[3] & a[2] & ~a[1] & a[0])
                               & ~(~a[3] & ~a[2] & a[1] & a[0])
                               & ~(a[3] & a[2] & a[1] & a[0]) )
    );

    ///// Input pattern to output mapping /////
    // For a==4'b1111, b==3'b010.
    check_all_ones_output: assert property (
        @(posedge CLK) (a[3] & a[2] & a[1] & a[0]) |-> (b == 3'b010)
    );
    // For exactly three ones, b==3'b101.
    check_three_ones_output: assert property (
        @(posedge CLK)
        ( (a[3] & a[2] & a[1] & ~a[0])
        | (a[3] & a[2] & ~a[1] & a[0])
        | (a[3] & ~a[2] & a[1] & a[0])
        | (~a[3] & a[2] & a[1] & a[0]) ) |-> (b == 3'b101)
    );
    // For exactly two ones, b==3'b110.
    check_two_ones_output: assert property (
        @(posedge CLK)
        ( (a[3] & a[2] & ~a[1] & ~a[0])
        | (a[3] & ~a[2] & a[1] & ~a[0])
        | (a[3] & ~a[2] & ~a[1] & a[0])
        | (~a[3] & a[2] & a[1] & ~a[0])
        | (~a[3] & a[2] & ~a[1] & a[0])
        | (~a[3] & ~a[2] & a[1] & a[0]) ) |-> (b == 3'b110)
    );
    // For zero or one '1' in a, b==3'b111.
    check_zero_or_one_ones_output: assert property (
        @(posedge CLK)
        !( (a[3] & a[2] & ~a[1] & ~a[0])
         | (a[3] & ~a[2] & a[1] & ~a[0])
         | (a[3] & ~a[2] & ~a[1] & a[0])
         | (~a[3] & a[2] & a[1] & ~a[0])
         | (~a[3] & a[2] & ~a[1] & a[0])
         | (~a[3] & ~a[2] & a[1] & a[0])
         | (a[3] & a[2] & a[1] & a[0])
         | (a[3] & a[2] & a[1] & ~a[0])
         | (a[3] & a[2] & ~a[1] & a[0])
         | (a[3] & ~a[2] & a[1] & a[0])
         | (~a[3] & a[2] & a[1] & a[0]) ) |-> (b == 3'b111)
    );

    ///// Output-to-input consistency (only when possible) /////
    // b[2]==0 only when a==4'b1111.
    check_b2_zero_means_all_ones: assert property (
        @(posedge CLK) (b[2] == 1'b0) |-> (a[3] & a[2] & a[1] & a[0])
    );
    // b[1]==0 only when exactly three ones.
    check_b1_zero_means_three_ones: assert property (
        @(posedge CLK)
        (b[1] == 1'b0) |-> ( (a[3] & a[2] & a[1] & ~a[0])
                           | (a[3] & a[2] & ~a[1] & a[0])
                           | (a[3] & ~a[2] & a[1] & a[0])
                           | (~a[3] & a[2] & a[1] & a[0]) )
    );
    // b[0]==0 only when exactly two ones or four ones.
    check_b0_zero_means_two_or_four_ones: assert property (
        @(posedge CLK)
        (b[0] == 1'b0) |-> ( (a[3] & a[2] & ~a[1] & ~a[0])
                           | (a[3] & ~a[2] & a[1] & ~a[0])
                           | (a[3] & ~a[2] & ~a[1] & a[0])
                           | (~a[3] & a[2] & a[1] & ~a[0])
                           | (~a[3] & a[2] & ~a[1] & a[0])
                           | (~a[3] & ~a[2] & a[1] & a[0])
                           | (a[3] & a[2] & a[1] & a[0]) )
    );
endmodule