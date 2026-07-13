module sub_sva (
    input logic CLK,
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [31:0] out1,
    input logic [31:0] out2
);
    // out1 lower 16 bits equal in1 & in2.
    check_out1_lower_and: assert property (
        @(posedge CLK) out1[15:0] == (in1 & in2)
    );
    // out1 upper 16 bits are zero.
    check_out1_upper_zero: assert property (
        @(posedge CLK) out1[31:16] == 16'h0000
    );
    // out2 lower 16 bits equal in1 | in2.
    check_out2_lower_or: assert property (
        @(posedge CLK) out2[15:0] == (in1 | in2)
    );
    // out2 upper 16 bits are zero.
    check_out2_upper_zero: assert property (
        @(posedge CLK) out2[31:16] == 16'h0000
    );
    // AND result is subset of OR result on lower bits.
    check_and_subset_or_lower: assert property (
        @(posedge CLK) (out1[15:0] & ~out2[15:0]) == 16'h0000
    );
    // (out1 | out2) equals out2.
    check_or_absorption: assert property (
        @(posedge CLK) (out1 | out2) == out2
    );
    // (out1 & out2) equals out1.
    check_and_absorption: assert property (
        @(posedge CLK) (out1 & out2) == out1
    );
    // (out1 ^ out2) lower equals in1 ^ in2.
    check_xor_identity_lower: assert property (
        @(posedge CLK) (out1[15:0] ^ out2[15:0]) == (in1 ^ in2)
    );
endmodule