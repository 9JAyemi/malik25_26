```systemverilog
module sky130_fd_sc_hd__a211oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    output logic Y
);
    // A1 and A2 must both be 0 for Y to be 1
    property p_and0;
        @(posedge clk) disable iff (!reset_n) (A1 & A2) |-> Y == 1'b0;
    endproperty
    assert property (p_and0) else $error("A1 and A2 must both be 0 for Y to be 1");

    // B1 or C1 must be 1 for Y to be 0
    property p_nor0;
        @(posedge clk) disable iff (!reset_n) !(B1 | C1) |-> Y == 1'b1;
    endproperty
    assert property (p_nor0) else $error("B1 or C1 must be 1 for Y to be 0");

    // A1 and A2 must both be 1 for Y to be 0
    property p_and0_inverted;
        @(posedge clk) disable iff (!reset_n) (A1 & A2) |-> Y == 1'b1;
    endproperty
    assert property (p_and0_inverted) else $error("A1 and A2 must both be 1 for Y to be 0");

    // B1 and C1 must both be 0 for Y to be 1
    property p_nor0_inverted;
        @(posedge clk) disable iff (!reset_n) !(B1 & C1) |-> Y == 1'b0;
    endproperty
    assert property (p_nor0_inverted) else $error("B1 and C1 must both be 0 for Y to be 1");

    // A1 must be 0 for Y to be 1
    property p_A1;
        @(posedge clk) disable iff (!reset_n) A1 |-> Y == 1'b0;
    endproperty
    assert property (p_A1) else $error("A1 must be 0 for Y to be 1");

    // A2 must be 0 for Y to be 1
    property p_A2;
        @(posedge clk) disable iff (!reset_n) A2 |-> Y == 1'b0;
    endproperty
    assert property (p_A2) else $error("A2 must be 0 for Y to be 1");

    // B1 must be 1 for Y to be 0
    property p_B1;
        @(posedge clk) disable iff (!reset_n) B1 |-> Y == 1'b1;
    endproperty
    assert property (p_B1) else $error("B1 must be 1 for Y to be 0");

    // C1 must be 1 for Y to be 0
    property p_C1;
        @(posedge clk) disable iff (!reset_n) C1 |-> Y == 1'b1;
    endproperty
    assert property (p_C1) else $error("C1 must be 1 for Y to be 0");

    // A1 and A2 must both be 0 for Y to be 1
    property p_and0_2;
        @(posedge clk) disable iff (!reset_n) (A1 & A2) |-> Y == 1'b0;
    endproperty
    assert property (p_and0_2) else $error("A1 and A2 must both be 0 for Y to be 1");

    // B1 or C1 must be 1 for Y to be 0
    property p_nor0_2;
        @(posedge clk) disable iff (!reset_n) !(B1 | C1) |-> Y == 1'b1;
    endproperty
    assert property (p_nor0_2) else $error("B1 or C1 must be 1 for Y to be 0");
endmodule
```