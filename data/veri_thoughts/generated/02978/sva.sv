module and4_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic Y
);
    // Combinational AND: no clock/reset; assertions sample on input posedges.

    // Y equals A1 & A2 & B1 & B2 (sampled on A1 posedge).
    check_y_func_on_A1_posedge: assert property (
        @(posedge A1) Y === (A1 & A2 & B1 & B2)
    );

    // Y equals A1 & A2 & B1 & B2 (sampled on A2 posedge).
    check_y_func_on_A2_posedge: assert property (
        @(posedge A2) Y === (A1 & A2 & B1 & B2)
    );

    // Y equals A1 & A2 & B1 & B2 (sampled on B1 posedge).
    check_y_func_on_B1_posedge: assert property (
        @(posedge B1) Y === (A1 & A2 & B1 & B2)
    );

    // Y equals A1 & A2 & B1 & B2 (sampled on B2 posedge).
    check_y_func_on_B2_posedge: assert property (
        @(posedge B2) Y === (A1 & A2 & B1 & B2)
    );

    // If either A1 or A2 is 0, Y must be 0 (sampled on A1 posedge).
    check_y_zero_when_A_pair_zero_on_A1: assert property (
        @(posedge A1) (!(A1 & A2)) |-> (Y == 1'b0)
    );

    // If either B1 or B2 is 0, Y must be 0 (sampled on B1 posedge).
    check_y_zero_when_B_pair_zero_on_B1: assert property (
        @(posedge B1) (!(B1 & B2)) |-> (Y == 1'b0)
    );

    // If A1 is 0 then Y is 0 (sampled on A2 posedge).
    check_y_zero_when_A1_zero_on_A2: assert property (
        @(posedge A2) (A1 == 1'b0) |-> (Y == 1'b0)
    );

    // If A2 is 0 then Y is 0 (sampled on A1 posedge).
    check_y_zero_when_A2_zero_on_A1: assert property (
        @(posedge A1) (A2 == 1'b0) |-> (Y == 1'b0)
    );

    // Y rising implies all inputs are 1 at that sample (sampled on A1 posedge).
    check_y_rise_requires_all_ones_on_A1: assert property (
        @(posedge A1) $rose(Y) |-> (A1 == 1'b1 && A2 == 1'b1 && B1 == 1'b1 && B2 == 1'b1)
    );

    // Y falling implies at least one input is 0 at that sample (sampled on A1 posedge).
    check_y_fall_requires_some_zero_on_A1: assert property (
        @(posedge A1) $fell(Y) |-> ((A1 == 1'b0) || (A2 == 1'b0) || (B1 == 1'b0) || (B2 == 1'b0))
    );
endmodule