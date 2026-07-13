module nor_and_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic Y
);

    // NOR gates
    wire nor1_out, nor2_out, nor3_out;

    // NOR gates
    nor nor1(nor1_out, A, B);
    nor nor2(nor2_out, C, D);
    nor nor3(Y, nor1_out, nor2_out);

    // No clock or reset signals present in the RTL
    // All logic is combinational

    // Check that Y is the result of the NOR operations
    check_nor_result: assert property (
        @(posedge VPWR) disable iff (!VGND) (Y == ~(nor1_out & nor2_out))
    );

    // Check that nor1_out is the result of the NOR of A and B
    check_nor1_result: assert property (
        @(posedge VPWR) disable iff (!VGND) (nor1_out == ~(A & B))
    );

    // Check that nor2_out is the result of the NOR of C and D
    check_nor2_result: assert property (
        @(posedge VPWR) disable iff (!VGND) (nor2_out == ~(C & D))
    );

endmodule