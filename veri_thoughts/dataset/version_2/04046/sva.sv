module logic_operation_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must match the implemented OR-of-ANDs logic.
    check_output_definition: assert property (
        @(posedge clk) Y == ((A & ~B) | (C & ~D))
    );

    // A high and B low must drive Y high.
    check_ab_term_sets_output: assert property (
        @(posedge clk) (A && !B) |-> Y
    );

    // C high and D low must drive Y high.
    check_cd_term_sets_output: assert property (
        @(posedge clk) (C && !D) |-> Y
    );

    // Y must be low when both product terms are false.
    check_output_low_when_both_terms_false: assert property (
        @(posedge clk) (!(A && !B) && !(C && !D)) |-> !Y
    );

endmodule