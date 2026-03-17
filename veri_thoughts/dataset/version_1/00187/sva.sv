module nor_and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must implement the full combinational function.
    check_output_function: assert property (
        @(posedge clk) Y == ((~(A | B)) & C & D)
    );

    // If either NOR input is high, the output must be low.
    check_a_or_b_blocks_output: assert property (
        @(posedge clk) (A || B) |-> !Y
    );

    // If C is low, the AND stage must force the output low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) !C |-> !Y
    );

    // If D is low, the AND stage must force the output low.
    check_d_low_blocks_output: assert property (
        @(posedge clk) !D |-> !Y
    );

    // When A and B are low, Y must match C AND D.
    check_ab_low_reduces_to_cd: assert property (
        @(posedge clk) (!A && !B) |-> (Y == (C && D))
    );

    // A high output requires both NOR inputs low and both AND inputs high.
    check_high_output_requires_all_enables: assert property (
        @(posedge clk) Y |-> (!A && !B && C && D)
    );

endmodule