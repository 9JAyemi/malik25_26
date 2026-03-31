```systemverilog
module and_gate_4_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    output logic Y
);
    // Ensure that Y is only driven by the AND operations
    property p_and_output;
        @(posedge clk) disable iff (!reset_n) Y == (A1 && A2 && A3 && B1 && C1);
    endproperty
    assert property (p_and_output) else $error("Y is not correctly driven by the AND operations");

    // Ensure that the intermediate signals are only driven by the AND operations
    property p_temp1;
        @(posedge clk) disable iff (!reset_n) temp1 == (A1 && A2);
    endproperty
    assert property (p_temp1) else $error("temp1 is not correctly driven by the AND operations");

    property p_temp2;
        @(posedge clk) disable iff (!reset_n) temp2 == (temp1 && A3);
    endproperty
    assert property (p_temp2) else $error("temp2 is not correctly driven by the AND operations");

    property p_temp3;
        @(posedge clk) disable iff (!reset_n) temp3 == (temp2 && B1);
    endproperty
    assert property (p_temp3) else $error("temp3 is not correctly driven by the AND operations");
endmodule
```