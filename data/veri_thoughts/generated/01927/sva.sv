module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);
    ///// Functional equivalence /////
    // F equals B^C^D when sampled on A rising edge.
    check_func_on_A_edge: assert property (
        @(posedge A) F == (B ^ C ^ D)
    );
    // F equals B^C^D when sampled on B rising edge.
    check_func_on_B_edge: assert property (
        @(posedge B) F == (B ^ C ^ D)
    );
    // F equals B^C^D when sampled on C rising edge.
    check_func_on_C_edge: assert property (
        @(posedge C) F == (B ^ C ^ D)
    );
    // F equals B^C^D when sampled on D rising edge.
    check_func_on_D_edge: assert property (
        @(posedge D) F == (B ^ C ^ D)
    );

    ///// Truth table by B,C, D (independent of A) /////
    // For BCD=000, F must be 0.
    truth_table_bcd_000: assert property (
        @(posedge A) ({B,C,D} == 3'b000) |-> (F == 1'b0)
    );
    // For BCD=001, F must be 1.
    truth_table_bcd_001: assert property (
        @(posedge A) ({B,C,D} == 3'b001) |-> (F == 1'b1)
    );
    // For BCD=010, F must be 1.
    truth_table_bcd_010: assert property (
        @(posedge A) ({B,C,D} == 3'b010) |-> (F == 1'b1)
    );
    // For BCD=011, F must be 0.
    truth_table_bcd_011: assert property (
        @(posedge A) ({B,C,D} == 3'b011) |-> (F == 1'b0)
    );
    // For BCD=100, F must be 1.
    truth_table_bcd_100: assert property (
        @(posedge A) ({B,C,D} == 3'b100) |-> (F == 1'b1)
    );
    // For BCD=101, F must be 0.
    truth_table_bcd_101: assert property (
        @(posedge A) ({B,C,D} == 3'b101) |-> (F == 1'b0)
    );
    // For BCD=110, F must be 0.
    truth_table_bcd_110: assert property (
        @(posedge A) ({B,C,D} == 3'b110) |-> (F == 1'b0)
    );
    // For BCD=111, F must be 1.
    truth_table_bcd_111: assert property (
        @(posedge A) ({B,C,D} == 3'b111) |-> (F == 1'b1)
    );
endmodule