module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic F
);

    // F must match the RTL case statement for all input combinations.
    check_function_equivalence: assert property (
        @(posedge clk)
        F == (({A, B, C} == 3'b000) ? (A & ~B & ~C) :
              (({A, B, C} == 3'b001) ? (A & ~B & C) :
              (({A, B, C} == 3'b010) ? (A & B & ~C) :
              (({A, B, C} == 3'b011) ? (A & B & C) :
              (({A, B, C} == 3'b100) ? (A & ~B & ~C) :
              (({A, B, C} == 3'b101) ? (A & ~B & C) :
              (({A, B, C} == 3'b110) ? (A & B & ~C) :
              (({A, B, C} == 3'b111) ? (A & B & C) : 1'b0)))))))))
    );

    // F must be low for input 000.
    check_f_low_for_000: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b000) |-> (F == 1'b0)
    );

    // F must be high for input 001.
    check_f_high_for_001: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b001) |-> (F == 1'b1)
    );

    // F must be low for input 010.
    check_f_low_for_010: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b010) |-> (F == 1'b0)
    );

    // F must be high for input 011.
    check_f_high_for_011: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b011) |-> (F == 1'b1)
    );

    // F must be low for input 100.
    check_f_low_for_100: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b100) |-> (F == 1'b0)
    );

    // F must be high for input 101.
    check_f_high_for_101: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b101) |-> (F == 1'b1)
    );

    // F must be low for input 110.
    check_f_low_for_110: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b110) |-> (F == 1'b0)
    );

    // F must be high for input 111.
    check_f_high_for_111: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b111) |-> (F == 1'b1)
    );

endmodule