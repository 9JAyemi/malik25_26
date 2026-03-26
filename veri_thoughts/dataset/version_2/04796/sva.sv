module complement_assertions (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] Y
);

    // Y must always be the bitwise complement of A.
    check_output_is_complement: assert property (
        @(posedge clk) (Y === ~A)
    );

    // Y[0] must invert A[0].
    check_bit0_complement: assert property (
        @(posedge clk) (Y[0] === ~A[0])
    );

    // Y[1] must invert A[1].
    check_bit1_complement: assert property (
        @(posedge clk) (Y[1] === ~A[1])
    );

    // Y[2] must invert A[2].
    check_bit2_complement: assert property (
        @(posedge clk) (Y[2] === ~A[2])
    );

    // Y[3] must invert A[3].
    check_bit3_complement: assert property (
        @(posedge clk) (Y[3] === ~A[3])
    );

    // If A is stable across samples, Y must also remain stable.
    check_stable_input_stable_output: assert property (
        @(posedge clk) $stable(A) |-> $stable(Y)
    );

endmodule