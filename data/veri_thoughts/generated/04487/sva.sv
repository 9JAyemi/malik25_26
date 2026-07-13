module sky130_fd_sc_hd__nor2b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B_N
);

    // Combinational RTL with no native clock or reset; sample on external clk.
    // Function implemented is Y = (~A) & B_N.

    // Y must match the implemented combinational function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ((~A) & B_N)
    );

    // A high forces Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> (Y == 1'b0)
    );

    // B_N low forces Y low.
    check_bn_low_forces_y_low: assert property (
        @(posedge clk) !B_N |-> (Y == 1'b0)
    );

    // A low with B_N high forces Y high.
    check_only_high_output_case: assert property (
        @(posedge clk) (!A && B_N) |-> (Y == 1'b1)
    );

    // Y high can only occur when A is low and B_N is high.
    check_y_high_implies_input_condition: assert property (
        @(posedge clk) Y |-> (!A && B_N)
    );

endmodule