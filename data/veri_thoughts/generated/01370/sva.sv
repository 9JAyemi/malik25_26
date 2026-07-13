module sky130_fd_sc_lp__and3b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // X equals AND of (A_N,B,C) where X is 1 only when all are exactly 1.
    check_truth_table_exact: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        (X === ((A_N === 1'b1) && (B === 1'b1) && (C === 1'b1)))
    );

    // If A_N is 0, X must be 0.
    check_x_low_when_a_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        (A_N === 1'b0) |-> (X === 1'b0)
    );

    // If B is 0, X must be 0.
    check_x_low_when_b_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        (B === 1'b0) |-> (X === 1'b0)
    );

    // If C is 0, X must be 0.
    check_x_low_when_c_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        (C === 1'b0) |-> (X === 1'b0)
    );

    // If X is 1 then all inputs are exactly 1.
    check_x_one_implies_inputs_one: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        (X === 1'b1) |-> ((A_N === 1'b1) && (B === 1'b1) && (C === 1'b1))
    );

    // If any input is not exactly 1 (including X/Z), X must be 0.
    check_x_zero_if_any_input_not_one: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ((A_N !== 1'b1) || (B !== 1'b1) || (C !== 1'b1)) |-> (X === 1'b0)
    );

    // X must never be X/Z because it is always assigned 0 or 1.
    check_x_never_unknown: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        !$isunknown(X)
    );

    // On A_N rising when B and C are 1, X must be 1.
    check_x_high_on_a_rise_when_bc_high: assert property (
        @(posedge A_N)
        disable iff (1'b0)
        ((B === 1'b1) && (C === 1'b1)) |-> (X === 1'b1)
    );

    // On B rising when A_N and C are 1, X must be 1.
    check_x_high_on_b_rise_when_ac_high: assert property (
        @(posedge B)
        disable iff (1'b0)
        ((A_N === 1'b1) && (C === 1'b1)) |-> (X === 1'b1)
    );

    // On C rising when A_N and B are 1, X must be 1.
    check_x_high_on_c_rise_when_ab_high: assert property (
        @(posedge C)
        disable iff (1'b0)
        ((A_N === 1'b1) && (B === 1'b1)) |-> (X === 1'b1)
    );
endmodule