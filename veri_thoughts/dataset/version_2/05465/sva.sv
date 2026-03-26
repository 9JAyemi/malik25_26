module karnaugh_map_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic F
);

    // F is high for input 000.
    check_f_high_000: assert property (
        @(posedge clk) ({A,B,C} == 3'b000) |-> (F == 1'b1)
    );

    // F is high for input 011.
    check_f_high_011: assert property (
        @(posedge clk) ({A,B,C} == 3'b011) |-> (F == 1'b1)
    );

    // F is low for all other input combinations.
    check_f_low_other_inputs: assert property (
        @(posedge clk)
        !((({A,B,C} == 3'b000) || ({A,B,C} == 3'b011))) |-> (F == 1'b0)
    );

    // F matches the implemented truth table each cycle.
    check_f_truth_table: assert property (
        @(posedge clk)
        F == (({A,B,C} == 3'b000) || ({A,B,C} == 3'b011))
    );

endmodule