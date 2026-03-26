module macc_simple_ena_sva (
    input logic        clk,
    input logic        ena,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] Z
);
    typedef logic [15:0] z_t;

    // Z follows the enabled accumulate or disabled hold behavior.
    check_z_update_matches_prior_enable: assert property (
        @(posedge clk) disable iff ($initstate)
        Z == ($past(ena) ? z_t'($past(Z) + ($past(A) * $past(B))) : $past(Z))
    );

    // With enable low on the prior clock, Z must hold.
    check_hold_when_prior_enable_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !$past(ena) |-> (Z == $past(Z))
    );

    // With enable high on the prior clock, Z must add the prior A*B.
    check_accumulate_when_prior_enable_high: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(ena) |-> (Z == z_t'($past(Z) + ($past(A) * $past(B))))
    );

    // Any observed change in Z must come from a prior enabled cycle.
    check_change_requires_prior_enable: assert property (
        @(posedge clk) disable iff ($initstate)
        (Z != $past(Z)) |-> $past(ena)
    );

endmodule