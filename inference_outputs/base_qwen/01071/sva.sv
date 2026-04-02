module sky130_fd_sc_ms__a211o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    output logic X
);
    // A1 and A2 must both be 1 for X to be 1
    property p_and;
        @(posedge clk) disable iff (!reset_n) (A1 & A2) |-> X == 1'b1;
    endproperty
    assert property (p_and) else $error("A1 and A2 must both be 1 for X to be 1");

    // If A1 or A2 is 0, X must be 0
    property p_or;
        @(posedge clk) disable iff (!reset_n) !(A1 | A2) |-> X == 1'b0;
    endproperty
    assert property (p_or) else $error("If A1 or A2 is 0, X must be 0");

    // If C1 is 1 and B1 is 0, X must be 0
    property p_c1_b1;
        @(posedge clk) disable iff (!reset_n) (C1 & !B1) |-> X == 1'b0;
    endproperty
    assert property (p_c1_b1) else $error("If C1 is 1 and B1 is 0, X must be 0");

    // If C1 is 0, X must be 1
    property p_c1_0;
        @(posedge clk) disable iff (!reset_n) !C1 |-> X == 1'b1;
    endproperty
    assert property (p_c1_0) else $error("If C1 is 0, X must be 1");

    // If B1 is 1, X must be 1
    property p_b1_1;
        @(posedge clk) disable iff (!reset_n) B1 |-> X == 1'b1;
    endproperty
    assert property (p_b1_1) else $error("If B1 is 1, X must be 1");

    // If A1 is 1 and A2 is 0, X must be 0
    property p_a1_a2;
        @(posedge clk) disable iff (!reset_n) (A1 & !A2) |-> X == 1'b0;
    endproperty
    assert property (p_a1_a2) else $error("If A1 is 1 and A2 is 0, X must be 0");

    // If A1 is 0 and A2 is 1, X must be 0
    property p_a1_a2_2;
        @(posedge clk) disable iff (!reset_n) (!A1 & A2) |-> X == 1'b0;
    endproperty
    assert property (p_a1_a2_2) else $error("If A1 is 0 and A2 is 1, X must be 0");

    // If A1 is 0 and A2 is 0, X must be 0
    property p_a1_a2_3;
        @(posedge clk) disable iff (!reset_n) (!A1 & !A2) |-> X == 1'b0;
    endproperty
    assert property (p_a1_a2_3) else $error("If A1 is 0 and A2 is 0, X must be 0");

    // If C1 is 1 and B1 is 1, X must be 1
    property p_c1_b1_1;
        @(posedge clk) disable iff (!reset_n) (C1 & B1) |-> X == 1'b1;
    endproperty
    assert property (p_c1_b1_1) else $error("If C1 is 1 and B1 is 1, X must be 1");

    // If C1 is 0 and B1 is 1, X must be 1
    property p_c1_b1_2;
        @(posedge clk) disable iff (!reset_n) (!C1 & B1) |-> X == 1'b1;
    endproperty
    assert property (p_c1_b1_2) else $error("If C1 is 0 and B1 is 1, X must be 1");

    // If C1 is 1 and B1 is 0, X must be 0
    property p_c1_b1_3;
        @(posedge clk) disable iff (!reset_n) (C1 & !B1) |-> X == 1'b0;
    endproperty
    assert property (p_c1_b1_3) else $error("If C1 is 1 and B1 is 0, X must be 0");

    // If C1 is 0 and B1 is 0, X must be 0
    property p_c1_b1_4;
        @(posedge clk) disable iff (!reset_n) (!C1 & !B1) |-> X == 1'b0;
    endproperty
    assert property (p_c1_b1_4) else $error("If C1 is 0 and B1 is 0, X must be 0");
endmodule