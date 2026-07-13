module arithmetic_module_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic [1:0] Y
);
    // Y = A1 - A2 when B1==1 and C1==0.
    check_subtract_branch: assert property (
        @(posedge CLK) (B1 && !C1) |-> (Y == (A1 - A2))
    );

    // Y = A1 * A2 when B1==1 and C1==1.
    check_multiply_branch: assert property (
        @(posedge CLK) (B1 && C1) |-> (Y == (A1 * A2))
    );

    // Y = A1 + A2 when B1==0.
    check_add_branch: assert property (
        @(posedge CLK) (!B1) |-> (Y == (A1 + A2))
    );

    // In add branch, LSB equals XOR of A1 and A2.
    check_add_bit0: assert property (
        @(posedge CLK) (!B1) |-> (Y[0] == (A1 ^ A2))
    );

    // In add branch, MSB equals carry (A1 & A2).
    check_add_bit1: assert property (
        @(posedge CLK) (!B1) |-> (Y[1] == (A1 & A2))
    );

    // In multiply branch, LSB equals A1 AND A2.
    check_mul_bit0: assert property (
        @(posedge CLK) (B1 && C1) |-> (Y[0] == (A1 & A2))
    );

    // In multiply branch, MSB is always 0 for 1-bit operands.
    check_mul_bit1_zero: assert property (
        @(posedge CLK) (B1 && C1) |-> (Y[1] == 1'b0)
    );

    // If inputs are stable across cycles, Y remains stable (combinational).
    check_y_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A1,A2,B1,C1}) |-> $stable(Y)
    );

    // Y always matches the operation selected by B1/C1.
    check_functional_selection: assert property (
        @(posedge CLK) (B1 && !C1) ? (Y == (A1 - A2)) :
                        (B1 &&  C1) ? (Y == (A1 * A2)) :
                                      (Y == (A1 + A2))
    );
endmodule