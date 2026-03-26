module sky130_fd_sc_lp__a21bo_lp_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic B1,
    input logic clk
);

    // External clk samples this combinational DUT; the RTL has no reset.

    // When the two B1 drivers agree, B1 must equal the shared driven value.
    check_b1_when_drivers_agree: assert property (
        @(posedge clk)
        (!$isunknown({A1, A2, B1_N}) && ((A1 & A2) == B1_N))
        |-> (B1 === ~B1_N)
    );

    // When the two B1 drivers agree, X must match B1_N through the final inverter.
    check_x_when_drivers_agree: assert property (
        @(posedge clk)
        (!$isunknown({A1, A2, B1_N}) && ((A1 & A2) == B1_N))
        |-> (X === B1_N)
    );

    // All three logical inputs high force B1 low and X high.
    check_all_high_case: assert property (
        @(posedge clk)
        ((A1 === 1'b1) && (A2 === 1'b1) && (B1_N === 1'b1))
        |-> ((B1 === 1'b0) && (X === 1'b1))
    );

    // B1_N low with either A1 or A2 low forces B1 high and X low.
    check_low_agree_case: assert property (
        @(posedge clk)
        (!$isunknown({A1, A2, B1_N}) && (B1_N === 1'b0) && ((A1 === 1'b0) || (A2 === 1'b0)))
        |-> ((B1 === 1'b1) && (X === 1'b0))
    );

    // A known low on B1 must invert to a high on X.
    check_x_high_when_b1_low: assert property (
        @(posedge clk)
        (B1 === 1'b0) |-> (X === 1'b1)
    );

    // A known high on B1 must invert to a low on X.
    check_x_low_when_b1_high: assert property (
        @(posedge clk)
        (B1 === 1'b1) |-> (X === 1'b0)
    );

endmodule