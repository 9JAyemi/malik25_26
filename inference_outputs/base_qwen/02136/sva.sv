```systemverilog
module binary_to_gray_sva (
    input logic [3:0] in,
    input logic [3:0] out
);
    // Binary to Gray conversion logic
    // out[0] should always be equal to in[0]
    property p_out0;
        @(posedge CLK) disable iff (!RESETn) out[0] == in[0];
    endproperty
    check_out0: assert property (p_out0) else $error("out[0] should be equal to in[0]");

    // out[1] should be the XOR of in[0] and in[1]
    property p_out1;
        @(posedge CLK) disable iff (!RESETn) out[1] == (in[0] ^ in[1]);
    endproperty
    check_out1: assert property (p_out1) else $error("out[1] should be the XOR of in[0] and in[1]");

    // out[2] should be the XOR of in[1], in[2], and in[0]
    property p_out2;
        @(posedge CLK) disable iff (!RESETn) out[2] == (in[1] ^ in[2] ^ in[0]);
    endproperty
    check_out2: assert property (p_out2) else $error("out[2] should be the XOR of in[1], in[2], and in[0]");

    // out[3] should be the XOR of in[2], in[3], and in[1]
    property p_out3;
        @(posedge CLK) disable iff (!RESETn) out[3] == (in[2] ^ in[3] ^ in[1]);
    endproperty
    check_out3: assert property (p_out3) else $error("out[3] should be the XOR of in[2], in[3], and in[1]");
endmodule
```