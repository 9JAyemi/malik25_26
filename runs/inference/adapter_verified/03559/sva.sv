module MUXCY_sva (
    input logic clk,
    input logic O,
    input logic CO,
    input logic CI,
    input logic DI,
    input logic S,
    input logic CIN
);

// O matches the implemented sum equation.
    check_o_function: assert property (
        @(posedge clk) O == ((S & DI) | (~S & CI))
    );

// CO matches the implemented carry equation.
    check_co_function: assert property (
        @(posedge clk) CO == (((CI & S) | (DI & (CI | S))))
    );

// When S is low, O follows CI.
    check_o_follows_ci_when_s_low: assert property (
        @(posedge clk) !S |-> (O == CI)
    );

// When S is high, O follows DI.
    check_o_follows_di_when_s_high: assert property (
        @(posedge clk) S |-> (O == DI)
    );

// When S is low, CO follows CI.
    check_co_follows_ci_when_s_low: assert property (
        @(posedge clk) !S |-> (CO == CI)
    );

// When S is high, CO follows DI.
    check_co_follows_di_when_s_high: assert property (
        @(posedge clk) S |-> (CO == DI)
    );

// With S low, CO is the AND of CI and DI.
    check_co_is_and_when_s_low: assert property (
        @(posedge clk) !S |-> (CO == (CI & DI))
    );

// With S high, CO is the OR of CI and DI.
    check_co_is_or_when_s_high: assert property (
        @(posedge clk) S |-> (CO == (CI | DI))
    );

endmodule
