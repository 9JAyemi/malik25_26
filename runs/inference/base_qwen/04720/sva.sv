module functional_module_sva (
    input [3:0] B,
    input [1:0] in,
    output reg [15:0] out
);
    // Check that BtoE converts B to E correctly
    property p_BtoE;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0000 |-> E == 4'b0011;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0001 |-> E == 4'b0100;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0010 |-> E == 4'b0101;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0011 |-> E == 4'b0110;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0100 |-> E == 4'b0111;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0101 |-> E == 4'b1000;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0110 |-> E == 4'b1001;
        @(posedge CLK) disable iff (!RESETn) B == 4'b0111 |-> E == 4'b1010;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1000 |-> E == 4'b1011;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1001 |-> E == 4'b1100;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1010 |-> E == 4'b1101;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1011 |-> E == 4'b1110;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1100 |-> E == 4'b1111;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1101 |-> E == 4'b0001;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1110 |-> E == 4'b0010;
        @(posedge CLK) disable iff (!RESETn) B == 4'b1111 |-> E == 4'b0011;
    endproperty
    assert property (p_BtoE) else $error("BtoE conversion error");

    // Check that decoder converts in to out correctly
    property p_decoder;
        @(posedge CLK) disable iff (!RESETn) in == 2'b00 |-> out == 16'b0000000000000001;
        @(posedge CLK) disable iff (!RESETn) in == 2'b01 |-> out == 16'b0000000000000010;
        @(posedge CLK) disable iff (!RESETn) in == 2'b10 |-> out == 16'b0000000000000100;
        @(posedge CLK) disable iff (!RESETn) in == 2'b11 |-> out == 16'b0000000000001000;
    endproperty
    assert property (p_decoder) else $error("Decoder conversion error");

    // Check that out is updated correctly based on D and E
    property p_out_update;
        @(posedge CLK) disable iff (!RESETn) out == D << E;
    endproperty
    assert property (p_out_update) else $error("Out update error");
endmodule