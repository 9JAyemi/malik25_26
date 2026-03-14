module or4_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);
    // Combinational DUT; assertions sample on CLK and are disabled when RESETn=0.

    // X equals A | B | ~C_N | ~D_N.
    check_or_function: assert property (
        @(posedge CLK) disable iff (!RESETn)
            X == (A | B | ~C_N | ~D_N)
    );

    // When A=0, B=0, C_N=1, D_N=1 then X=0.
    check_all_inactive_gives_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!A && !B && C_N && D_N) |=> (X == 1'b0)
    );

    // If A is 1, X must be 1.
    check_A_drives_X: assert property (
        @(posedge CLK) disable iff (!RESETn)
            A |=> (X == 1'b1)
    );

    // If B is 1, X must be 1.
    check_B_drives_X: assert property (
        @(posedge CLK) disable iff (!RESETn)
            B |=> (X == 1'b1)
    );

    // If C_N is 0, X must be 1.
    check_Cn_low_drives_X: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!C_N) |=> (X == 1'b1)
    );

    // If D_N is 0, X must be 1.
    check_Dn_low_drives_X: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!D_N) |=> (X == 1'b1)
    );

    // If X is 0, inputs must be A=0, B=0, C_N=1, D_N=1.
    check_x_zero_implies_inputs_inactive: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b0) |=> (!A && !B && C_N && D_N)
    );

    // If X is 1, at least one driver is active.
    check_x_one_implies_some_active: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b1) |=> (A || B || !C_N || !D_N)
    );

    // With C_N=1 and D_N=1, X reduces to A|B.
    check_reduction_when_CnDn_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C_N && D_N) |=> (X == (A | B))
    );

    // Stable inputs imply stable X.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $stable({A,B,C_N,D_N}) |=> $stable(X)
    );

    // X rising is caused by A/B rising or C_N/D_N falling.
    check_x_rise_caused_by_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $rose(X) |=> ($rose(A) || $rose(B) || $fell(C_N) || $fell(D_N))
    );

    // X falling is caused by A/B falling or C_N/D_N rising.
    check_x_fall_caused_by_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $fell(X) |=> ($fell(A) || $fell(B) || $rose(C_N) || $rose(D_N))
    );
endmodule