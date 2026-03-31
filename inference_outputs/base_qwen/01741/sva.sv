```systemverilog
module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    output logic ECK
);
    // ECK is the output of the logic, which is a function of E, SE, and CK.
    // ECK is HIGH when (E AND SE) is HIGH or (NOT E AND CK) is HIGH.
    logic_property: assert property (
        @(posedge CK) disable iff (!CK) (ECK == ((E & SE) | (!E & CK)))
    );
endmodule
```