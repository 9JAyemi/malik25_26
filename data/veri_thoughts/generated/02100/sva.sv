module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic a,
    input logic b,
    input logic cin,
    input logic select,
    input logic [31:0] out
);
    // When select=0, out is the byte-reversed form of in.
    check_select0_byte_swap: assert property (
        @(posedge clk) disable iff (reset) (!select) |-> (out == {in[7:0], in[15:8], in[23:16], in[31:24]})
    );

    // When select=1, the lower 24 bits of out must be zero.
    check_select1_lower_bytes_zero: assert property (
        @(posedge clk) disable iff (reset) (select) |-> (out[23:0] == 24'b0)
    );

    // When select=1, the upper 5 bits of the top byte of out must be zero.
    check_select1_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset) (select) |-> (out[31:27] == 5'b0)
    );

    // When select=1, the low 3 bits of the top byte of out equal {a,b,cin}.
    check_select1_upper_byte_abc_mapping: assert property (
        @(posedge clk) disable iff (reset) (select) |-> (out[26:24] == {a, b, cin})
    );

    // When select=1 and a=b=cin=0, out must be all zeros.
    check_select1_abc_zero_produces_zero: assert property (
        @(posedge clk) disable iff (reset) (select && !a && !b && !cin) |-> (out == 32'b0)
    );

    // When select=1 and a=b=cin=1, out must equal 0x07000000.
    check_select1_abc_ones_value: assert property (
        @(posedge clk) disable iff (reset) (select && a && b && cin) |-> (out == 32'h0700_0000)
    );

    // When select=0 and in is zero, out must be zero (byte-reversing zero yields zero).
    check_select0_zero_input_zero_output: assert property (
        @(posedge clk) disable iff (reset) (!select && (in == 32'b0)) |-> (out == 32'b0)
    );
endmodule