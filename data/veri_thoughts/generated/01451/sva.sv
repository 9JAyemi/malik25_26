module sky130_fd_sc_ls__nor3_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);
    // Y equals NOR of A,B,C each cycle.
    check_nor_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~(A | B | C)
    );

    // When all inputs are 0, Y must be 1.
    check_y_one_when_all_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A && !B && !C) |-> (Y == 1'b1)
    );

    // When any input is 1, Y must be 0.
    check_y_zero_when_any_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (A | B | C) |-> (Y == 1'b0)
    );

    // If Y is 1, then all inputs must be 0.
    check_y1_implies_all_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b1) |-> (!A && !B && !C)
    );

    // If Y is 0, then at least one input must be 1.
    check_y0_implies_any_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b0) |-> (A | B | C)
    );

    // If A,B,C are stable, Y must also be stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({A,B,C}) |-> $stable(Y)
    );
endmodule