module sky130_fd_sc_ls__a2111oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // No clock/reset in DUT; pure combinational; assertions use $global_clock.
    // Y is NOR of {B1, C1, D1, (A1 & A2)}.
    
    // Functional equivalence: Y == ~(B1 | C1 | D1 | (A1 & A2)).
    check_function_equivalence: assert property (
        @($global_clock) Y == ~(B1 | C1 | D1 | (A1 & A2))
    );

    // If any contributor is 1, Y must be 0.
    check_any_high_forces_low: assert property (
        @($global_clock) (B1 || C1 || D1 || (A1 && A2)) |-> (Y == 1'b0)
    );

    // If all contributors are 0, Y must be 1.
    check_all_low_forces_high: assert property (
        @($global_clock) (!B1 && !C1 && !D1 && !(A1 && A2)) |-> (Y == 1'b1)
    );

    // Y high implies all contributors are 0.
    check_y_high_implies_all_low: assert property (
        @($global_clock) (Y == 1'b1) |-> (!B1 && !C1 && !D1 && !(A1 && A2))
    );

    // Y low implies at least one contributor is 1.
    check_y_low_implies_any_high: assert property (
        @($global_clock) (Y == 1'b0) |-> (B1 || C1 || D1 || (A1 && A2))
    );

    // B1=1 forces Y=0.
    check_b1_forces_low: assert property (
        @($global_clock) B1 |-> (Y == 1'b0)
    );

    // C1=1 forces Y=0.
    check_c1_forces_low: assert property (
        @($global_clock) C1 |-> (Y == 1'b0)
    );

    // D1=1 forces Y=0.
    check_d1_forces_low: assert property (
        @($global_clock) D1 |-> (Y == 1'b0)
    );

    // A1&A2=1 forces Y=0.
    check_a_pair_forces_low: assert property (
        @($global_clock) (A1 && A2) |-> (Y == 1'b0)
    );

    // If inputs are stable, Y must be stable (pure combinational).
    check_stable_inputs_imply_stable_output: assert property (
        @($global_clock) $stable({A1, A2, B1, C1, D1}) |-> $stable(Y)
    );

    // Y can only rise when all contributors are 0.
    check_y_rise_when_all_low: assert property (
        @($global_clock) $rose(Y) |-> (!B1 && !C1 && !D1 && !(A1 && A2))
    );

    // Y can only fall when at least one contributor is 1.
    check_y_fall_when_any_high: assert property (
        @($global_clock) $fell(Y) |-> (B1 || C1 || D1 || (A1 && A2))
    );
endmodule