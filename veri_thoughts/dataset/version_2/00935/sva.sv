module sky130_fd_sc_ls__a311oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // Y implements ~( (A1 & A2 & A3) | B1 | C1 )
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & A3) | B1 | C1)
    );

    // If B1 is HIGH, Y must be LOW.
    check_y_zero_when_b1_high: assert property (
        @(posedge clk) B1 |-> (Y == 1'b0)
    );

    // If C1 is HIGH, Y must be LOW.
    check_y_zero_when_c1_high: assert property (
        @(posedge clk) C1 |-> (Y == 1'b0)
    );

    // If A1&A2&A3 are all HIGH, Y must be LOW.
    check_y_zero_when_all_a_high: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // Y can be HIGH only when B1=0, C1=0, and not all of A1,A2,A3 are 1.
    check_y_implication_from_y_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!B1 && !C1 && !(A1 & A2 & A3))
    );

    // When B1=0, C1=0, and not all of A1,A2,A3 are 1, Y must be HIGH.
    check_y_one_when_allowed: assert property (
        @(posedge clk) (!B1 && !C1 && !(A1 & A2 & A3)) |-> (Y == 1'b1)
    );

    // With B1=0 and C1=0, Y equals ~(A1 & A2 & A3).
    check_y_when_b1c1_zero: assert property (
        @(posedge clk) (!B1 && !C1) |-> (Y == ~(A1 & A2 & A3))
    );

    // If inputs are stable across a cycle, Y must remain stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A1, A2, A3, B1, C1}) |-> $stable(Y)
    );
endmodule