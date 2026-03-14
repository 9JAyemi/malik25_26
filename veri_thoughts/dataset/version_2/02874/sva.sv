module karnaugh_map_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic F
);
    // F must be 0 when A,B,C = 000.
    check_map_000: assert property (
        @(posedge CLK) ({A,B,C} === 3'b000) |-> (F == 1'b0)
    );

    // F must be 1 when A,B,C = 001.
    check_map_001: assert property (
        @(posedge CLK) ({A,B,C} === 3'b001) |-> (F == 1'b1)
    );

    // F must be 0 when A,B,C = 010.
    check_map_010: assert property (
        @(posedge CLK) ({A,B,C} === 3'b010) |-> (F == 1'b0)
    );

    // F must be 1 when A,B,C = 011.
    check_map_011: assert property (
        @(posedge CLK) ({A,B,C} === 3'b011) |-> (F == 1'b1)
    );

    // F must be 0 when A,B,C = 100.
    check_map_100: assert property (
        @(posedge CLK) ({A,B,C} === 3'b100) |-> (F == 1'b0)
    );

    // F must be 1 when A,B,C = 101.
    check_map_101: assert property (
        @(posedge CLK) ({A,B,C} === 3'b101) |-> (F == 1'b1)
    );

    // F must be 1 when A,B,C = 110.
    check_map_110: assert property (
        @(posedge CLK) ({A,B,C} === 3'b110) |-> (F == 1'b1)
    );

    // F must be 0 when A,B,C = 111.
    check_map_111: assert property (
        @(posedge CLK) ({A,B,C} === 3'b111) |-> (F == 1'b0)
    );

    // F equals C XOR (A AND B) for all known inputs.
    check_function_equivalence: assert property (
        @(posedge CLK) !($isunknown({A,B,C})) |-> (F == (C ^ (A & B)))
    );
endmodule