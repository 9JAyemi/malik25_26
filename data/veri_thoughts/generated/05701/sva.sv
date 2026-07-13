module v0dbcb9_sva (
    input logic clk,
    input logic [1:0] v8b19dd,
    input logic v3f8943,
    input logic v64d863
);

    // v3f8943 matches the low input bit.
    check_v3f8943_matches_bit0: assert property (
        @(posedge clk) v3f8943 == v8b19dd[0]
    );

    // v64d863 is high when the two input bits are equal.
    check_v64d863_matches_xnor: assert property (
        @(posedge clk) v64d863 == (v8b19dd[1] ~^ v8b19dd[0])
    );

    // Input 2'b00 maps to v3f8943=0 and v64d863=1.
    check_input_00_mapping: assert property (
        @(posedge clk) (v8b19dd == 2'b00) |-> (v3f8943 == 1'b0 && v64d863 == 1'b1)
    );

    // Input 2'b01 maps to v3f8943=1 and v64d863=0.
    check_input_01_mapping: assert property (
        @(posedge clk) (v8b19dd == 2'b01) |-> (v3f8943 == 1'b1 && v64d863 == 1'b0)
    );

    // Input 2'b10 maps to v3f8943=0 and v64d863=0.
    check_input_10_mapping: assert property (
        @(posedge clk) (v8b19dd == 2'b10) |-> (v3f8943 == 1'b0 && v64d863 == 1'b0)
    );

    // Input 2'b11 maps to v3f8943=1 and v64d863=1.
    check_input_11_mapping: assert property (
        @(posedge clk) (v8b19dd == 2'b11) |-> (v3f8943 == 1'b1 && v64d863 == 1'b1)
    );

endmodule