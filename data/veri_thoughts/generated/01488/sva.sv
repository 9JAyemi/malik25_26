module arithmetic_circuit_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // Y equals the LSB of ((A1+A2+A3)*B1 - (A1*C1)).
    check_y_matches_expr_lsb: assert property (
        @(posedge VPWR) Y == ((((A1 + A2 + A3) * B1) - (A1 * C1))[0])
    );

    // Y simplifies to ((A1^A2^A3)&B1) ^ (A1&C1).
    check_y_simplified_boolean: assert property (
        @(posedge VPWR) Y == ( ((A1 ^ A2 ^ A3) & B1) ^ (A1 & C1) )
    );

    // If B1 is 0, Y equals (A1 & C1).
    check_when_B1_zero: assert property (
        @(posedge VPWR) (B1 == 1'b0) |-> (Y == (A1 & C1))
    );

    // If C1 is 0, Y equals ((A1 + A2 + A3) & B1).
    check_when_C1_zero: assert property (
        @(posedge VPWR) (C1 == 1'b0) |-> (Y == ((A1 + A2 + A3) & B1))
    );

    // If B1 is 1, Y equals (A1 + A2 + A3) XOR (A1 & C1).
    check_when_B1_one: assert property (
        @(posedge VPWR) (B1 == 1'b1) |-> (Y == ((A1 + A2 + A3) ^ (A1 & C1)))
    );

    // If B1 and C1 are both 0, Y must be 0.
    check_when_B1_C1_zero: assert property (
        @(posedge VPWR) (B1 == 1'b0 && C1 == 1'b0) |-> (Y == 1'b0)
    );

    // If B1 is 1 and C1 is 1, Y equals (A1 + A2 + A3) XOR A1.
    check_when_B1_C1_one: assert property (
        @(posedge VPWR) (B1 == 1'b1 && C1 == 1'b1) |-> (Y == ((A1 + A2 + A3) ^ A1))
    );

    // If A1 is 0, Y equals ((A2 + A3) & B1).
    check_when_A1_zero: assert property (
        @(posedge VPWR) (A1 == 1'b0) |-> (Y == ((A2 + A3) & B1))
    );

    // If A1 is 1 and C1 is 0, Y equals ((~(A2 ^ A3)) & B1).
    check_when_A1_one_C1_zero: assert property (
        @(posedge VPWR) (A1 == 1'b1 && C1 == 1'b0) |-> (Y == ((~(A2 ^ A3)) & B1))
    );
endmodule