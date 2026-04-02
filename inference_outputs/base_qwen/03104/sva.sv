module OR3_gate_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The OR3_gate module is purely combinational logic.
    // The output X is the result of the OR operation on inputs A, B, and C.
    // No clock or reset signals are present in the OR3_gate module.
    // Therefore, we use a clocked assertion to ensure the combinational logic is correct.

    // Combinational logic assertion
    comb_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (X == (A | B | C))
    ) else $error("Combinational logic error in OR3_gate");
endmodule