module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // X implements (A1 & A2) | A3.
    check_function_exact: assert property (
        @(posedge clk) X == ((A1 & A2) | A3)
    );

    // If A3 is HIGH, X must be HIGH.
    check_A3_forces_X_high: assert property (
        @(posedge clk) A3 |-> (X == 1'b1)
    );

    // If A3 is LOW, X reduces to A1 & A2.
    check_A3_zero_reduces_to_and: assert property (
        @(posedge clk) (A3 == 1'b0) |-> (X == (A1 & A2))
    );

    // If A1 & A2 is 0, X equals A3.
    check_and_zero_equals_A3: assert property (
        @(posedge clk) ((A1 & A2) == 1'b0) |-> (X == A3)
    );

    // X is 1 only if A3 is 1 or (A1 & A2) is 1.
    check_X_one_implies_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A3 == 1'b1) || (A1 & A2))
    );

    // If A1, A2, A3 are stable, X is stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A1, A2, A3}) |-> $stable(X)
    );

    // X does not depend on B1 when A1,A2,A3 are stable.
    check_independence_B1: assert property (
        @(posedge clk) $changed(B1) && $stable({A1, A2, A3}) |-> $stable(X)
    );

    // X does not depend on B2 when A1,A2,A3 are stable.
    check_independence_B2: assert property (
        @(posedge clk) $changed(B2) && $stable({A1, A2, A3}) |-> $stable(X)
    );

    // X does not depend on VPWR when A1,A2,A3 are stable.
    check_independence_VPWR: assert property (
        @(posedge clk) $changed(VPWR) && $stable({A1, A2, A3}) |-> $stable(X)
    );

    // X does not depend on VGND when A1,A2,A3 are stable.
    check_independence_VGND: assert property (
        @(posedge clk) $changed(VGND) && $stable({A1, A2, A3}) |-> $stable(X)
    );
endmodule