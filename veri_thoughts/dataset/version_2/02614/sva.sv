module sky130_fd_sc_ms__o2111ai_sva (
    input logic CLK,     // No clock/reset in DUT; use external clock for SVA sampling
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y equals ~(C1 & B1 & D1 & (A1 | A2)).
    check_function_equation: assert property (
        @(posedge CLK) Y === ~(C1 & B1 & D1 & (A1 | A2))
    );

    // If both A inputs are 0, Y must be 1.
    check_y_one_when_A_both_zero: assert property (
        @(posedge CLK) (A1 == 1'b0 && A2 == 1'b0) |-> (Y == 1'b1)
    );

    // If B1 is 0, Y must be 1.
    check_y_one_when_B1_zero: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // If C1 is 0, Y must be 1.
    check_y_one_when_C1_zero: assert property (
        @(posedge CLK) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // If D1 is 0, Y must be 1.
    check_y_one_when_D1_zero: assert property (
        @(posedge CLK) (D1 == 1'b0) |-> (Y == 1'b1)
    );

    // If all NAND inputs are 1 (i.e., B1=C1=D1=1 and A1|A2=1), Y must be 0.
    check_y_zero_when_all_high: assert property (
        @(posedge CLK) (B1 == 1'b1 && C1 == 1'b1 && D1 == 1'b1 && (A1 == 1'b1 || A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // With all inputs known (0/1), Y must be known (not X/Z).
    check_no_x_when_inputs_known: assert property (
        @(posedge CLK) (! $isunknown({A1, A2, B1, C1, D1})) |-> (! $isunknown(Y))
    );

    // If A1 rises with A2=0 and B1=C1=D1=1, Y must fall.
    check_y_falls_on_A1_rise_others_high: assert property (
        @(posedge CLK) ($rose(A1) && (A2 == 1'b0) && (B1 == 1'b1) && (C1 == 1'b1) && (D1 == 1'b1)) |-> $fell(Y)
    );

    // If A2 rises with A1=0 and B1=C1=D1=1, Y must fall.
    check_y_falls_on_A2_rise_others_high: assert property (
        @(posedge CLK) ($rose(A2) && (A1 == 1'b0) && (B1 == 1'b1) && (C1 == 1'b1) && (D1 == 1'b1)) |-> $fell(Y)
    );

    // If B1 rises with C1=D1=1 and (A1|A2)=1, Y must fall.
    check_y_falls_on_B1_rise_others_high: assert property (
        @(posedge CLK) ($rose(B1) && (C1 == 1'b1) && (D1 == 1'b1) && (A1 == 1'b1 || A2 == 1'b1)) |-> $fell(Y)
    );

    // If C1 rises with B1=D1=1 and (A1|A2)=1, Y must fall.
    check_y_falls_on_C1_rise_others_high: assert property (
        @(posedge CLK) ($rose(C1) && (B1 == 1'b1) && (D1 == 1'b1) && (A1 == 1'b1 || A2 == 1'b1)) |-> $fell(Y)
    );

    // If D1 rises with B1=C1=1 and (A1|A2)=1, Y must fall.
    check_y_falls_on_D1_rise_others_high: assert property (
        @(posedge CLK) ($rose(D1) && (B1 == 1'b1) && (C1 == 1'b1) && (A1 == 1'b1 || A2 == 1'b1)) |-> $fell(Y)
    );

    // If A1 falls with A2=0 and B1=C1=D1=1, Y must rise.
    check_y_rises_on_A1_fall_others_high: assert property (
        @(posedge CLK) ($fell(A1) && (A2 == 1'b0) && (B1 == 1'b1) && (C1 == 1'b1) && (D1 == 1'b1)) |-> $rose(Y)
    );

    // If B1 falls with C1=D1=1 and (A1|A2)=1, Y must rise.
    check_y_rises_on_B1_fall_others_high: assert property (
        @(posedge CLK) ($fell(B1) && (C1 == 1'b1) && (D1 == 1'b1) && (A1 == 1'b1 || A2 == 1'b1)) |-> $rose(Y)
    );

endmodule