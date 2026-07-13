module and3b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

// X must be 1 when all three data inputs are 1.
    check_all_high_sets_x_high: assert property (
        @(posedge clk) (A_N == 1'b1 && B == 1'b1 && C == 1'b1) |-> (X == 1'b1)
    );

// X must be 0 when any data input is 0.
    check_any_low_sets_x_low: assert property (
        @(posedge clk) (A_N == 1'b0 || B == 1'b0 || C == 1'b0) |-> (X == 1'b0)
    );

// X must be 0 when any data input is X.
    check_any_x_sets_x_unknown: assert property (
        @(posedge clk) ($isunknown(A_N) || $isunknown(B) || $isunknown(C)) |-> $isunknown(X)
    );

// X must be 1 when all three data inputs are 1.
    check_all_high_sets_x_high: assert property (
        @(posedge clk) (A_N == 1'b1 && B == 1'b1 && C == 1'b1) |-> (X == 1'b1)
    );

// X must be 0 when any data input is 0.
    check_any_low_sets_x_low: assert property (
        @(posedge clk) (A_N == 1'b0 || B == 1'b0 || C == 1'b0) |-> (X == 1'b0)
    );

// X must be 0 when any data input is X.
    check_any_x_sets_x_unknown: assert property (
        @(posedge clk) ($isunknown(A_N) || $isunknown(B) || $isunknown(C)) |-> $isunknown(X)
    );

// X must be 1 when all three data inputs are 1.
    check_all_high_sets_x_high: assert property (
        @(posedge clk) (A_N == 1'b1 && B == 1'b1 && C == 1'b1) |-> (X == 1'b1)
    );

// X must be 0 when any data input is 0.
    check_any_low_sets_x_low: assert property (
        @(posedge clk) (A_N == 1'b0 || B == 1'b0 || C == 1'b0) |-> (X == 1'b0)
    );

// X must be 0 when any data input is X.
    check_any_x_sets_x_unknown: assert property (
        @(posedge clk) ($isunknown(A_N) || $isunknown(B) || $isunknown(C)) |-> $isunknown(X)
    );

endmodule
