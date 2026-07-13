module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);
    // F implements F = C ^ D ^ (B & ~A)
    check_function_equivalence: assert property (
        @(posedge clk) F == ((C ^ D) ^ (B & ~A))
    );

    // When B==0, F equals C ^ D
    check_B0_parity: assert property (
        @(posedge clk) (B == 1'b0) |-> (F == (C ^ D))
    );

    // When A==1, F equals C ^ D
    check_A1_parity: assert property (
        @(posedge clk) (A == 1'b1) |-> (F == (C ^ D))
    );

    // When A==0 and B==1, F equals ~(C ^ D)
    check_A0B1_inversion: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b1)) |-> (F == ~(C ^ D))
    );

    // When A==0 and B==0, F equals C ^ D
    check_A0B0_parity: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (F == (C ^ D))
    );

    // When C==D, F equals (B & ~A)
    check_C_eq_D_term: assert property (
        @(posedge clk) (C == D) |-> (F == (B & ~A))
    );

    // When C!=D, F equals ~(B & ~A)
    check_C_ne_D_term: assert property (
        @(posedge clk) (C != D) |-> (F == ~(B & ~A))
    );

    // If inputs stable cycle-to-cycle, F must remain stable
    check_pure_function_stability: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(F)
    );

    // Exact mapping: 4'b0000 -> F=0
    check_map_0000: assert property (
        @(posedge clk) ({A,B,C,D} == 4'b0000) |-> (F == 1'b0)
    );

    // Exact mapping: 4'b0001 -> F=1
    check_map_0001: assert property (
        @(posedge clk) ({A,B,C,D} == 4'b0001) |-> (F == 1'b1)
    );

    // Exact mapping: 4'b0010 -> F=1
    check_map_0010: assert property (
        @(posedge clk) ({A,B,C,D} == 4'b0010) |-> (F == 1'b1)
    );

    // Exact mapping: 4'b1111 -> F=0
    check_map_1111: assert property (
        @(posedge clk) ({A,B,C,D} == 4'b1111) |-> (F == 1'b0)
    );
endmodule