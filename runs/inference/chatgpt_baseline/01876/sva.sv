module sky130_fd_sc_lp__a21boi_sva (
    input  logic CLK,
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1_N
);
    // Functional equivalence: Y = ~(~B1_N | (A1 & A2)).
    check_eq_nor_form: assert property (
        @(posedge CLK) Y == ~( (~B1_N) | (A1 & A2) )
    );

    // Functional equivalence (DeMorgan): Y = B1_N & (~A1 | ~A2).
    check_eq_demorgan_form: assert property (
        @(posedge CLK) Y == (B1_N & ((~A1) | (~A2)))
    );

    // B1_N LOW forces Y LOW.
    check_b1n_low_forces_y_low: assert property (
        @(posedge CLK) (!B1_N) |-> (Y == 1'b0)
    );

    // A1&A2 HIGH forces Y LOW.
    check_and_high_forces_y_low: assert property (
        @(posedge CLK) (A1 && A2) |-> (Y == 1'b0)
    );

    // When no AND (A1==0 or A2==0), Y passes B1_N.
    check_passthrough_when_no_and: assert property (
        @(posedge CLK) (!(A1 && A2)) |-> (Y == B1_N)
    );

    // If B1_N HIGH and no AND, Y must be HIGH.
    check_high_condition: assert property (
        @(posedge CLK) (B1_N && !(A1 && A2)) |-> (Y == 1'b1)
    );

    // Y HIGH implies B1_N HIGH and no AND.
    check_y_high_implies_inputs: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (B1_N && (!A1 || !A2))
    );

    // Y LOW implies B1_N LOW or A1&A2 HIGH.
    check_y_low_implies_inputs: assert property (
        @(posedge CLK) (Y == 1'b0) |-> ((!B1_N) || (A1 && A2))
    );

    // If B1_N HIGH and Y LOW, then A1&A2 must be HIGH.
    check_b1n_high_y_low_implies_and: assert property (
        @(posedge CLK) (B1_N && (Y == 1'b0)) |-> (A1 && A2)
    );

    // Y rising edge only when B1_N HIGH and no AND.
    check_y_rise_condition: assert property (
        @(posedge CLK) $rose(Y) |-> (B1_N && (!A1 || !A2))
    );

    // Y falling edge only when B1_N LOW or A1&A2 HIGH.
    check_y_fall_condition: assert property (
        @(posedge CLK) $fell(Y) |-> ((!B1_N) || (A1 && A2))
    );
endmodule