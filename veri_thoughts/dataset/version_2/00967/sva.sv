module sky130_fd_sc_ls__o2111ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // Y equals ~(C1 & B1 & D1 & (A1 | A2)).
    check_functional_equivalence: assert property (
        @(posedge clk) Y == !(C1 && B1 && D1 && (A1 || A2))
    );

    // Y==0 implies C1=B1=D1=1 and (A1|A2)=1.
    check_y_zero_implies_all_inputs_one: assert property (
        @(posedge clk) (Y == 1'b0) |-> (C1 && B1 && D1 && (A1 || A2))
    );

    // Y==1 implies at least one of C1,B1,D1 is 0 or both A1 and A2 are 0.
    check_y_one_implies_any_zero: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!C1 || !B1 || !D1 || (!A1 && !A2))
    );

    // C1 low forces Y high (NAND controlling input).
    check_c1_low_forces_one: assert property (
        @(posedge clk) (!C1) |-> (Y == 1'b1)
    );

    // B1 low forces Y high (NAND controlling input).
    check_b1_low_forces_one: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // D1 low forces Y high (NAND controlling input).
    check_d1_low_forces_one: assert property (
        @(posedge clk) (!D1) |-> (Y == 1'b1)
    );

    // A1 and A2 both low force Y high (OR input to NAND is 0).
    check_a_both_low_forces_one: assert property (
        @(posedge clk) (!A1 && !A2) |-> (Y == 1'b1)
    );

    // All ones with (A1|A2)=1 force Y low.
    check_all_high_and_or_high_forces_zero: assert property (
        @(posedge clk) (C1 && B1 && D1 && (A1 || A2)) |-> (Y == 1'b0)
    );

    // A1 high with other NAND inputs high forces Y low.
    check_a1_high_others_high_forces_zero: assert property (
        @(posedge clk) (A1 && B1 && C1 && D1) |-> (Y == 1'b0)
    );

    // A2 high with other NAND inputs high forces Y low.
    check_a2_high_others_high_forces_zero: assert property (
        @(posedge clk) (A2 && B1 && C1 && D1) |-> (Y == 1'b0)
    );
endmodule