module signal_processing_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // No RTL reset exists; assertions are always active.
    // Y must match the RTL's full combinational expression.
    check_y_matches_rtl_expr: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((A1_N & A2_N) ? (B1 | B2) :
              (A1_N & ~A2_N) ? B1 :
              (~A1_N & A2_N) ? B2 : 1'b0)
    );

    // When both select inputs are high, Y is B1 OR B2.
    check_or_path_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N && A2_N) |-> (Y == (B1 | B2))
    );

    // When only A1_N is high, Y follows B1.
    check_b1_path_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N && !A2_N) |-> (Y == B1)
    );

    // When only A2_N is high, Y follows B2.
    check_b2_path_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A1_N && A2_N) |-> (Y == B2)
    );

    // When both select inputs are low, Y is forced low.
    check_no_path_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A1_N && !A2_N) |-> (Y == 1'b0)
    );

endmodule