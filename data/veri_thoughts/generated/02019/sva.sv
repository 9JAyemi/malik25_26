module sky130_fd_sc_hd__and2b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B
);
    // X equals (~A_N) & B
    check_function_equation: assert property (
        @(posedge clk) X == ((~A_N) & B)
    );

    // When B is 0, X must be 0
    check_x_zero_when_b_zero: assert property (
        @(posedge clk) (B == 1'b0) |-> (X == 1'b0)
    );

    // When A_N is 1, X must be 0
    check_x_zero_when_a_n_one: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // When A_N is 0 and B is 1, X must be 1
    check_x_one_when_a0_b1: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // On B rising edge with A_N==0, X must be 1
    check_x_one_on_b_rise_when_a0: assert property (
        @(posedge clk) ($rose(B) && (A_N == 1'b0)) |-> (X == 1'b1)
    );

    // On B falling edge, X must be 0
    check_x_zero_on_b_fall: assert property (
        @(posedge clk) $fell(B) |-> (X == 1'b0)
    );

    // On A_N falling edge with B==1, X must be 1
    check_x_one_on_an_fall_when_b1: assert property (
        @(posedge clk) ($fell(A_N) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // On A_N rising edge with B==1, X must be 0
    check_x_zero_on_an_rise_when_b1: assert property (
        @(posedge clk) ($rose(A_N) && (B == 1'b1)) |-> (X == 1'b0)
    );

    // X can only rise when B==1 and A_N==0
    check_x_rise_requires_b1_a0: assert property (
        @(posedge clk) $rose(X) |-> ((B == 1'b1) && (A_N == 1'b0))
    );

    // X can only fall when B==0 or A_N==1
    check_x_fall_requires_b0_or_a1: assert property (
        @(posedge clk) $fell(X) |-> ((B == 1'b0) || (A_N == 1'b1))
    );
endmodule