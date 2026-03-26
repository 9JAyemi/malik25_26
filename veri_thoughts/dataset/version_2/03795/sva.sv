module shift_left_2_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] X
);

    // X[3] matches the assigned AND of A[1] and A[0].
    check_x3_equation: assert property (
        @(posedge clk) X[3] == (A[1] & A[0])
    );

    // X[2] matches the assigned AND of A[0] and the inverse of A[1].
    check_x2_equation: assert property (
        @(posedge clk) X[2] == (A[0] & (~A[1]))
    );

    // X[1] matches the assigned AND of the inverses of A[2] and A[1].
    check_x1_equation: assert property (
        @(posedge clk) X[1] == ((~A[2]) & (~A[1]))
    );

    // X[0] matches the assigned AND of the inverses of A[3] and A[2].
    check_x0_equation: assert property (
        @(posedge clk) X[0] == ((~A[3]) & (~A[2]))
    );

    // X matches the complete combinational assignment from A.
    check_x_vector_equation: assert property (
        @(posedge clk) X == { (A[1] & A[0]), (A[0] & (~A[1])), ((~A[2]) & (~A[1])), ((~A[3]) & (~A[2])) }
    );

    // X[3] and X[2] cannot both be high because they require opposite values of A[1].
    check_upper_bits_mutex: assert property (
        @(posedge clk) !(X[3] && X[2])
    );

endmodule