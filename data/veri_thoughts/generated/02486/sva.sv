module sky130_fd_sc_ls__a41oi_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // Y equals NOR of B1 and (A1 & A2 & A3 & A4).
    check_func_equation: assert property (
        @(posedge CLK) Y == ~(B1 | (A1 & A2 & A3 & A4))
    );

    // B1=1 forces Y=0.
    check_b1_dominates: assert property (
        @(posedge CLK) B1 |-> (Y == 1'b0)
    );

    // All A's high forces Y=0.
    check_and4_dominates: assert property (
        @(posedge CLK) (A1 & A2 & A3 & A4) |-> (Y == 1'b0)
    );

    // B1=0 and not(all A's high) forces Y=1.
    check_high_sufficient: assert property (
        @(posedge CLK) (!B1 && !(A1 & A2 & A3 & A4)) |-> (Y == 1'b1)
    );

    // Y=1 requires B1=0 and not(all A's high).
    check_high_necessary: assert property (
        @(posedge CLK) Y |-> (!B1 && !(A1 & A2 & A3 & A4))
    );

    // Y=0 requires B1=1 or all A's high.
    check_low_necessary: assert property (
        @(posedge CLK) !Y |-> (B1 || (A1 & A2 & A3 & A4))
    );

    // When B1=0, Y equals NOT of (A1 & A2 & A3 & A4).
    check_case_b1_low_equation: assert property (
        @(posedge CLK) !B1 |-> (Y == ~(A1 & A2 & A3 & A4))
    );

    // When not(all A's high), Y equals NOT of B1.
    check_case_and4_low_equation: assert property (
        @(posedge CLK) !(A1 & A2 & A3 & A4) |-> (Y == ~B1)
    );
endmodule