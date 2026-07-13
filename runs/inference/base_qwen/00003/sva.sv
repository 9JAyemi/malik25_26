module sky130_fd_sc_hd__o21bai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset signals are present in the RTL

    // The logic is purely combinational as there are no sequential elements

    // Key signals and interfaces:
    // Y, A1, A2, B1_N are inputs
    // VPWR, VGND, VPB, VNB are power and ground signals

    // Functional behaviors:
    // Y is the output of a combinational logic circuit

    // Combinational logic behavior:
    // Y = !B1_N && (A2 || A1)

    // Assertion for the combinational logic behavior
    comb_logic: assert property (
        @(posedge VPWR) disable iff (VGND) (Y == (!B1_N && (A2 || A1)))
    ) else $error("Combinational logic behavior violated");

endmodule