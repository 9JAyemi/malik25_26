```systemverilog
module split_16bit_to_8bit_sva (
    input wire [15:0] in,
    input wire [7:0] out_hi,
    input wire [7:0] out_lo
);
    // Decoder to select the high byte
    wire [1:0] select_hi;
    assign select_hi = in[15:14];

    // Decoder to select the low byte
    wire [1:0] select_lo;
    assign select_lo = in[13:12];

    // Multiplexer to select the high byte
    wire [7:0] hi_byte;
    assign hi_byte = {in[15:8], 8'b0};
    assign out_hi = hi_byte[select_hi];

    // Multiplexer to select the low byte
    wire [7:0] lo_byte;
    assign lo_byte = {8'b0, in[7:0]};
    assign out_lo = lo_byte[select_lo];

    // Property to check if out_hi is correctly set based on in[15:8]
    property p_out_hi;
        @(posedge clk) disable iff (!reset_n) out_hi == in[15:8];
    endproperty
    assert property (p_out_hi) else $error("out_hi is not correctly set based on in[15:8]");

    // Property to check if out_lo is correctly set based on in[7:0]
    property p_out_lo;
        @(posedge clk) disable iff (!reset_n) out_lo == in[7:0];
    endproperty
    assert property (p_out_lo) else $error("out_lo is not correctly set based on in[7:0]");

    // Property to check if select_hi is correctly set based on in[15:14]
    property p_select_hi;
        @(posedge clk) disable iff (!reset_n) select_hi == in[15:14];
    endproperty
    assert property (p_select_hi) else $error("select_hi is not correctly set based on in[15:14]");

    // Property to check if select_lo is correctly set based on in[13:12]
    property p_select_lo;
        @(posedge clk) disable iff (!reset_n) select_lo == in[13:12];
    endproperty
    assert property (p_select_lo) else $error("select_lo is not correctly set based on in[13:12]");

    // Property to check if hi_byte is correctly set based on in[15:8]
    property p_hi_byte;
        @(posedge clk) disable iff (!reset_n) hi_byte == {in[15:8], 8'b0};
    endproperty
    assert property (p_hi_byte) else $error("hi_byte is not correctly set based on in[15:8]");

    // Property to check if lo_byte is correctly set based on in[7:0]
    property p_lo_byte;
        @(posedge clk) disable iff (!reset_n) lo_byte == {8'b0, in[7:0]};
    endproperty
    assert property (p_lo_byte) else $error("lo_byte is not correctly set based on in[7:0]");
endmodule
```