module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Combinational function checks (clocked on $global_clock) /////
    // Y implements ~(B1 & (A1 | A2 | A3)).
    check_func_equiv: assert property (
        @(posedge $global_clock) Y == ~(B1 & (A1 | A2 | A3))
    );

    // B1 low forces Y high.
    check_b1_low_forces_high: assert property (
        @(posedge $global_clock) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // All A inputs low force Y high.
    check_all_a_low_forces_high: assert property (
        @(posedge $global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

    // B1 high and any A high force Y low.
    check_b1_high_and_any_a_high_forces_low: assert property (
        @(posedge $global_clock) ((B1 == 1'b1) && (A1 || A2 || A3)) |-> (Y == 1'b0)
    );

    // Y low implies B1 high and some A high.
    check_y_low_implies_conditions: assert property (
        @(posedge $global_clock) (Y == 1'b0) |-> ((B1 == 1'b1) && (A1 || A2 || A3))
    );

    // Only A1 high (A2,A3 low) makes Y == ~B1.
    check_only_a1_high_behaviour: assert property (
        @(posedge $global_clock) ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == ~B1)
    );

    // Only A2 high (A1,A3 low) makes Y == ~B1.
    check_only_a2_high_behaviour: assert property (
        @(posedge $global_clock) ((A1 == 1'b0) && (A2 == 1'b1) && (A3 == 1'b0)) |-> (Y == ~B1)
    );

    // Only A3 high (A1,A2 low) makes Y == ~B1.
    check_only_a3_high_behaviour: assert property (
        @(posedge $global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b1)) |-> (Y == ~B1)
    );

    // All A high and B1 low drive Y high.
    check_all_a_high_b1_low_drives_y_high: assert property (
        @(posedge $global_clock) ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1) && (B1 == 1'b0)) |-> (Y == 1'b1)
    );
endmodule