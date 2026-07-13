module register_module_assertions (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

    // Outputs start at zero from the initial block.
    check_initial_outputs_zero: assert property (
        @(posedge clk) $initstate |-> (A == 4'd0) && (B == 4'd0) && (C == 4'd0)
    );

    // A increments by one on each clock.
    check_a_increments_each_cycle: assert property (
        @(posedge clk) 1'b1 |=> (A == ($past(A) + 4'd1))
    );

    // B decrements by one on each clock.
    check_b_decrements_each_cycle: assert property (
        @(posedge clk) 1'b1 |=> (B == ($past(B) - 4'd1))
    );

    // C always reflects the sum of A and B.
    check_c_matches_sum: assert property (
        @(posedge clk) C == (A + B)
    );

    // The combined A+B value is preserved from cycle to cycle.
    check_sum_preserved_each_cycle: assert property (
        @(posedge clk) 1'b1 |=> ((A + B) == ($past(A) + $past(B)))
    );

endmodule