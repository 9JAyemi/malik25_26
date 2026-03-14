module sky130_fd_sc_ms__o21bai_sva (
    input  logic CLK,
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1_N
);
    // Y equals B1_N | (~A1 & ~A2).
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) Y == (B1_N | ((!A1) & (!A2)))
    );

    // Y equals ~( (~B1_N) & (A1 | A2) ).
    check_demorgan_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ~( (~B1_N) & (A1 | A2) )
    );

    // B1_N high forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge CLK) disable iff (1'b0) (B1_N == 1'b1) |-> (Y == 1'b1)
    );

    // When B1_N is low, Y equals NOR(A1, A2).
    check_b1n_low_gives_nor: assert property (
        @(posedge CLK) disable iff (1'b0) (B1_N == 1'b0) |-> (Y == !(A1 || A2))
    );

    // If B1_N is low and (A1 or A2) is high, Y must be low.
    check_enable_low_and_any_input_high_makes_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1_N == 1'b0) && ((A1 == 1'b1) || (A2 == 1'b1))) |-> (Y == 1'b0)
    );

    // If both A1 and A2 are low, Y must be high.
    check_both_inputs_low_makes_y_high: assert property (
        @(posedge CLK) disable iff (1'b0) ((!A1) && (!A2)) |-> (Y == 1'b1)
    );

    // Y low implies B1_N is low and at least one of A1/A2 is high.
    check_y_low_characterization: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b0) |-> ((B1_N == 1'b0) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

    // Y high implies B1_N is high or both A1 and A2 are low.
    check_y_high_characterization: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b1) |-> ((B1_N == 1'b1) || ((!A1) && (!A2)))
    );

    // With B1_N low and both A1 and A2 high, Y must be low.
    check_b1n_low_and_both_high_makes_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1_N == 1'b0) && (A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // Rising A1 under B1_N low forces Y low that cycle.
    check_a1_rise_under_b1n_low_forces_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) ($rose(A1) && (B1_N == 1'b0)) |-> (Y == 1'b0)
    );

    // Rising A2 under B1_N low forces Y low that cycle.
    check_a2_rise_under_b1n_low_forces_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) ($rose(A2) && (B1_N == 1'b0)) |-> (Y == 1'b0)
    );
endmodule