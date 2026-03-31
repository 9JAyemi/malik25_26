```systemverilog
module eight_to_one_sva (
    input logic [2:0] A1,
    input logic [2:0] A2,
    input logic [2:0] B1,
    input logic [2:0] B2,
    input logic [2:0] C1,
    input logic [2:0] C2,
    input logic [2:0] D1,
    input logic [2:0] D2,
    output logic [2:0] Y
);

    // Find the maximum of the A group
    property p_max_A;
        @(posedge clk) disable iff (!reset_n) (A1 > A2) |-> (Y == A1);
    endproperty
    assert property (p_max_A) else $error("A1 is greater than A2 but Y is not A1");

    // Find the maximum of the B group
    property p_max_B;
        @(posedge clk) disable iff (!reset_n) (B1 > B2 && B1 > Y) |-> (Y == B1);
    endproperty
    assert property (p_max_B) else $error("B1 is greater than B2 and Y is not B1");

    // Find the maximum of the C group
    property p_max_C;
        @(posedge clk) disable iff (!reset_n) (C1 > C2 && C1 > Y) |-> (Y == C1);
    endproperty
    assert property (p_max_C) else $error("C1 is greater than C2 and Y is not C1");

    // Find the maximum of the D group
    property p_max_D;
        @(posedge clk) disable iff (!reset_n) (D1 > D2 && D1 > Y) |-> (Y == D1);
    endproperty
    assert property (p_max_D) else $error("D1 is greater than D2 and Y is not D1");

    // Ensure Y is updated correctly when B2 is greater than Y
    property p_update_Y_B2;
        @(posedge clk) disable iff (!reset_n) (B2 > Y) |-> (Y == B2);
    endproperty
    assert property (p_update_Y_B2) else $error("B2 is greater than Y but Y is not B2");

    // Ensure Y is updated correctly when C2 is greater than Y
    property p_update_Y_C2;
        @(posedge clk) disable iff (!reset_n) (C2 > Y) |-> (Y == C2);
    endproperty
    assert property (p_update_Y_C2) else $error("C2 is greater than Y but Y is not C2");

    // Ensure Y is updated correctly when D2 is greater than Y
    property p_update_Y_D2;
        @(posedge clk) disable iff (!reset_n) (D2 > Y) |-> (Y == D2);
    endproperty
    assert property (p_update_Y_D2) else $error("D2 is greater than Y but Y is not D2");

endmodule
```