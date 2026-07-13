module MX2X4A12TR_sva (
    input logic clk,   // external clock for sampling
    input logic A,
    input logic B,
    input logic S0,
    input logic Y
);
    // Y must equal B | S0 (4-state aware).
    check_y_equals_b_or_s0: assert property (
        @(posedge clk) disable iff (1'b0) (Y === (B | S0))
    );

    // When both B and S0 are 0, Y must be 0.
    check_y_zero_when_both_zero: assert property (
        @(posedge clk) disable iff (1'b0) ((B === 1'b0) && (S0 === 1'b0)) |-> (Y === 1'b0)
    );

    // When B is 1, Y must be 1.
    check_y_one_when_b_one: assert property (
        @(posedge clk) disable iff (1'b0) (B === 1'b1) |-> (Y === 1'b1)
    );

    // When S0 is 1, Y must be 1.
    check_y_one_when_s0_one: assert property (
        @(posedge clk) disable iff (1'b0) (S0 === 1'b1) |-> (Y === 1'b1)
    );

    // If Y is 0, then both B and S0 must be 0.
    check_y_zero_implies_inputs_zero: assert property (
        @(posedge clk) disable iff (1'b0) (Y === 1'b0) |-> ((B === 1'b0) && (S0 === 1'b0))
    );

    // If Y is 1, then at least one of B or S0 must be 1.
    check_y_one_implies_any_input_one: assert property (
        @(posedge clk) disable iff (1'b0) (Y === 1'b1) |-> ((B === 1'b1) || (S0 === 1'b1))
    );

    // When S0 is 0, Y must equal B.
    check_y_eq_b_when_s0_zero: assert property (
        @(posedge clk) disable iff (1'b0) (S0 === 1'b0) |-> (Y === B)
    );

    // When B is 0, Y must equal S0.
    check_y_eq_s0_when_b_zero: assert property (
        @(posedge clk) disable iff (1'b0) (B === 1'b0) |-> (Y === S0)
    );

    // Y must remain stable when B and S0 are stable.
    check_y_stable_when_b_s0_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(B) && $stable(S0)) |-> $stable(Y)
    );

    // Y must be independent of A; A changes with B and S0 stable must not change Y.
    check_independence_from_a: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(A) && $stable(B) && $stable(S0)) |-> $stable(Y)
    );
endmodule