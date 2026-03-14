module sky130_fd_sc_hd__a2111oi_0_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Combinational cell; no clock/reset in RTL. Sample on any input edge; no reset disable (disable iff 1'b0).

    // Y must equal (A1 & A2) | (~A1 & ~A2 & B1 & ~C1 & ~D1).
    check_functional_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        Y == ( (A1 & A2) | (~A1 & ~A2 & B1 & ~C1 & ~D1) )
    );

    // If A1 and A2 are HIGH, Y must be HIGH (dominant first term).
    check_y_high_when_a1a2_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (A1 & A2) |-> (Y == 1'b1)
    );

    // If ~A1 & ~A2 & B1 & ~C1 & ~D1, Y must be HIGH (second minterm).
    check_y_high_when_second_minterm: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        ((~A1 & ~A2 & B1 & ~C1 & ~D1)) |-> (Y == 1'b1)
    );

    // If neither minterm is true, Y must be LOW.
    check_y_low_when_no_minterm: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (~(A1 & A2) & ~(~A1 & ~A2 & B1 & ~C1 & ~D1)) |-> (Y == 1'b0)
    );

    // If Y is HIGH, at least one minterm must be true (no spurious 1s).
    check_y_high_implies_minterm: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (Y == 1'b1) |-> ((A1 & A2) || (~A1 & ~A2 & B1 & ~C1 & ~D1))
    );

    // If exactly one of A1/A2 is HIGH, Y must be LOW.
    check_y_low_when_a1_xor_a2: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (A1 ^ A2) |-> (Y == 1'b0)
    );

    // If A1==0, A2==0, and B1==0, Y must be LOW.
    check_y_low_when_b0_and_a_both_0: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (~A1 & ~A2 & ~B1) |-> (Y == 1'b0)
    );

    // If A1==0, A2==0, and C1==1 or D1==1, Y must be LOW.
    check_y_low_when_a_both_0_and_c_or_d_1: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1
          or negedge A1 or negedge A2 or negedge B1 or negedge C1 or negedge D1)
        disable iff (1'b0)
        (~A1 & ~A2 & (C1 | D1)) |-> (Y == 1'b0)
    );

endmodule