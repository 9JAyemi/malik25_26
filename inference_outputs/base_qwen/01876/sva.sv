module sky130_fd_sc_lp__a21boi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as there are no sequential elements.

    // A1 and A2 must be inputs to the AND gate.
    combinational_input_and: assert property (
        @(posedge VPWR) disable iff (VGND) (A1 && A2)
    );

    // B1_N must be an input to the NOT gate.
    combinational_input_not: assert property (
        @(posedge VPWR) disable iff (VGND) (!B1_N)
    );

    // The output Y should be the result of the NOR gate.
    combinational_output_nor: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == !(!B1_N || A1 && A2))
    );

endmodule