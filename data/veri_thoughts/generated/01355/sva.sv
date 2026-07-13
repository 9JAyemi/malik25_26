module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    // Y equals (A1_N & A2_N) | (~B1 & ~B2).
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Y === ((A1_N & A2_N) | (~B1 & ~B2))
    );

    // If both A inputs are HIGH, Y must be HIGH.
    check_Y_high_when_A_both_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A1_N === 1'b1 && A2_N === 1'b1) |-> (Y === 1'b1)
    );

    // If both B inputs are LOW, Y must be HIGH.
    check_Y_high_when_B_both_low: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B1 === 1'b0 && B2 === 1'b0) |-> (Y === 1'b1)
    );

    // If any B input is HIGH, Y equals A1_N & A2_N.
    check_Y_equals_A_and_when_any_B_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((B1 === 1'b1) || (B2 === 1'b1)) |-> (Y === (A1_N & A2_N))
    );

    // If any A input is LOW, Y equals ~B1 & ~B2.
    check_Y_equals_B_nor_when_any_A_low: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A1_N === 1'b0) || (A2_N === 1'b0)) |-> (Y === (~B1 & ~B2))
    );

    // If both A inputs are LOW and any B is HIGH, Y must be LOW.
    check_Y_low_when_A_both_low_and_any_B_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A1_N === 1'b0) && (A2_N === 1'b0) && ((B1 === 1'b1) || (B2 === 1'b1))) |-> (Y === 1'b0)
    );
endmodule