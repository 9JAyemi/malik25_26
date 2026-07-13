module v9a2795_sva (
    input logic clk,
    input logic [2:0] vdee7c7,
    input logic vda577d,
    input logic v3f8943,
    input logic v64d863
);
    // o2 equals majority-of-three of input bits
    check_o2_majority: assert property (
        @(posedge clk) vda577d == ((vdee7c7[1] & vdee7c7[2]) | (vdee7c7[0] & vdee7c7[2]) | (vdee7c7[0] & vdee7c7[1]))
    );

    // o0 equals b & (c ^ a)
    check_o0_expr: assert property (
        @(posedge clk) v64d863 == (vdee7c7[1] & (vdee7c7[2] ^ vdee7c7[0]))
    );

    // o1 equals a & (c ^ b)
    check_o1_expr: assert property (
        @(posedge clk) v3f8943 == (vdee7c7[0] & (vdee7c7[2] ^ vdee7c7[1]))
    );

    // o0 high implies b is high
    check_o0_requires_b: assert property (
        @(posedge clk) v64d863 |-> vdee7c7[1]
    );

    // o1 high implies a is high
    check_o1_requires_a: assert property (
        @(posedge clk) v3f8943 |-> vdee7c7[0]
    );

    // If fewer than two inputs are 1, all outputs are 0
    check_less_than_two_means_zero: assert property (
        @(posedge clk) !((vdee7c7[0] & vdee7c7[1]) | (vdee7c7[0] & vdee7c7[2]) | (vdee7c7[1] & vdee7c7[2]))
        |-> (vda577d == 1'b0) && (v64d863 == 1'b0) && (v3f8943 == 1'b0)
    );

    // If all three inputs are 1, o2=1 and o0=o1=0
    check_all_ones_outputs: assert property (
        @(posedge clk) (vdee7c7 == 3'b111) |-> (vda577d == 1'b1) && (v64d863 == 1'b0) && (v3f8943 == 1'b0)
    );

    // o0|o1 is 1 exactly when exactly two inputs are 1
    check_o0o1_or_exactly2: assert property (
        @(posedge clk) (v64d863 | v3f8943) ==
            ((vdee7c7[0] & vdee7c7[1] & ~vdee7c7[2]) |
             (vdee7c7[0] & vdee7c7[2] & ~vdee7c7[1]) |
             (vdee7c7[1] & vdee7c7[2] & ~vdee7c7[0]))
    );

    // o2 equals (o0|o1) OR (all three inputs are 1)
    check_o2_rel_o0o1_allones: assert property (
        @(posedge clk) vda577d == ((v64d863 | v3f8943) | (vdee7c7[0] & vdee7c7[1] & vdee7c7[2]))
    );

    // o0^o1 equals c & (a^b)
    check_o0o1_xor_c_ab: assert property (
        @(posedge clk) (v64d863 ^ v3f8943) == (vdee7c7[2] & (vdee7c7[0] ^ vdee7c7[1]))
    );

    // o0&o1 equals a&b&~c
    check_o0o1_and_ab_nc: assert property (
        @(posedge clk) (v64d863 & v3f8943) == (vdee7c7[0] & vdee7c7[1] & ~vdee7c7[2])
    );
endmodule