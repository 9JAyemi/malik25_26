module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B,
    input logic O
);
    // No clock/reset in RTL; pure combinational: w0 = A1|A2; O = ~((A1|A2) & B).

    // O equals ~((A1|A2) & B) on A1 rising edge.
    check_func_eq_on_A1_rise: assert property (
        @(posedge A1) O == ~((A1 | A2) & B)
    );

    // O equals ~((A1|A2) & B) on A1 falling edge.
    check_func_eq_on_A1_fall: assert property (
        @(negedge A1) O == ~((A1 | A2) & B)
    );

    // O equals ~((A1|A2) & B) on A2 rising edge.
    check_func_eq_on_A2_rise: assert property (
        @(posedge A2) O == ~((A1 | A2) & B)
    );

    // O equals ~((A1|A2) & B) on A2 falling edge.
    check_func_eq_on_A2_fall: assert property (
        @(negedge A2) O == ~((A1 | A2) & B)
    );

    // O equals ~((A1|A2) & B) on B rising edge.
    check_func_eq_on_B_rise: assert property (
        @(posedge B) O == ~((A1 | A2) & B)
    );

    // O equals ~((A1|A2) & B) on B falling edge.
    check_func_eq_on_B_fall: assert property (
        @(negedge B) O == ~((A1 | A2) & B)
    );

    // When B goes LOW, NAND output must be HIGH.
    check_B_low_forces_O_high_on_B_fall: assert property (
        @(negedge B) O == 1'b1
    );

    // If B is LOW, O must be HIGH (checked on A1 rising edge).
    check_B0_forces_O1_on_A1_rise: assert property (
        @(posedge A1) (B == 1'b0) |-> (O == 1'b1)
    );

    // If B is LOW, O must be HIGH (checked on A2 rising edge).
    check_B0_forces_O1_on_A2_rise: assert property (
        @(posedge A2) (B == 1'b0) |-> (O == 1'b1)
    );

    // If O is LOW when B is HIGH, at least one of A1/A2 must be HIGH (checked on B rising edge).
    check_O_low_requires_A1_or_A2_when_B_high: assert property (
        @(posedge B) (O == 1'b0) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );
endmodule