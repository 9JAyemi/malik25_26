module mux_4to1_case_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] sel,
    input logic clk,
    input logic Y
);
    // Clock: clk (posedge). No reset in RTL.
    // Mixed logic: combinational sel propagation; sequential update of Y on clk.

    // When sel==00, next-cycle Y equals current A.
    y_updates_on_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |=> (Y == $past(A))
    );

    // When sel==01, next-cycle Y equals current B.
    y_updates_on_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |=> (Y == $past(B))
    );

    // When sel==10, next-cycle Y equals current C.
    y_updates_on_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |=> (Y == $past(C))
    );

    // When sel==11, next-cycle Y equals current D.
    y_updates_on_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |=> (Y == $past(D))
    );

    // If sel stays 00 and A is stable across cycles, Y remains stable.
    y_stable_when_sel00_and_A_stable: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $stable(A)) |=> $stable(Y)
    );

    // If sel stays 01 and B is stable across cycles, Y remains stable.
    y_stable_when_sel01_and_B_stable: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $stable(B)) |=> $stable(Y)
    );

    // If sel stays 10 and C is stable across cycles, Y remains stable.
    y_stable_when_sel10_and_C_stable: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $stable(C)) |=> $stable(Y)
    );

    // If sel stays 11 and D is stable across cycles, Y remains stable.
    y_stable_when_sel11_and_D_stable: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $stable(D)) |=> $stable(Y)
    );

endmodule