module nor4b_sva (
    input logic CLK,   // external sampling clock for SVA
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset in RTL; pure combinational. Assertions sampled on external CLK.
    // Functional behavior: Y = ~(A | B | C | D_N). Power pins unused in logic.

    // Y equals bitwise NOR of A,B,C,D_N.
    check_function_nor4b: assert property (
        @(posedge CLK) disable iff (1'b0) (Y === ~(A | B | C | D_N))
    );

    // If any input is HIGH, Y must be LOW.
    check_any_high_forces_low: assert property (
        @(posedge CLK) disable iff (1'b0) (|{A,B,C,D_N}) |-> (Y == 1'b0)
    );

    // If all inputs are LOW, Y must be HIGH.
    check_all_low_forces_high: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B && !C && !D_N) |-> (Y == 1'b1)
    );

    // If Y is HIGH, then all inputs are LOW.
    check_y_high_implies_all_low: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b1) |-> (!A && !B && !C && !D_N)
    );

    // If Y is LOW, then at least one input is HIGH.
    check_y_low_implies_any_high: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b0) |-> (|{A,B,C,D_N})
    );

    // A rising to HIGH forces Y LOW.
    check_rose_A_forces_low: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(A) |-> (Y == 1'b0)
    );

    // B rising to HIGH forces Y LOW.
    check_rose_B_forces_low: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(B) |-> (Y == 1'b0)
    );

    // C rising to HIGH forces Y LOW.
    check_rose_C_forces_low: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(C) |-> (Y == 1'b0)
    );

    // D_N rising to HIGH forces Y LOW.
    check_rose_DN_forces_low: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(D_N) |-> (Y == 1'b0)
    );

endmodule