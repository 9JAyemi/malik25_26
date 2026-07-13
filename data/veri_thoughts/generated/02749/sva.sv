module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic F
);
    // No clock/reset in DUT; sample on any edge of A/B/C.
    // Pure combinational logic: F=1 for 010,011,100,111; else 0.

    // F equals simplified boolean function: F = (B & C) | (~C & (A ^ B)).
    check_function_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            F == ((B & C) | ((~C) & (A ^ B)))
    );

    // Truth table: 000 -> F=0.
    truth_000_is_0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b000) |=> (F == 1'b0)
    );

    // Truth table: 001 -> F=0.
    truth_001_is_0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b001) |=> (F == 1'b0)
    );

    // Truth table: 010 -> F=1.
    truth_010_is_1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b010) |=> (F == 1'b1)
    );

    // Truth table: 011 -> F=1.
    truth_011_is_1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b011) |=> (F == 1'b1)
    );

    // Truth table: 100 -> F=1.
    truth_100_is_1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b100) |=> (F == 1'b1)
    );

    // Truth table: 101 -> F=0.
    truth_101_is_0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b101) |=> (F == 1'b0)
    );

    // Truth table: 110 -> F=0.
    truth_110_is_0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b110) |=> (F == 1'b0)
    );

    // Truth table: 111 -> F=1.
    truth_111_is_1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            ({A,B,C} == 3'b111) |=> (F == 1'b1)
    );
endmodule