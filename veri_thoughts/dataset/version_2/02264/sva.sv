module twos_complement_sva (
    input logic [3:0] in,
    input logic [3:0] out
);
    ///// Functional equivalence /////
    // out equals bitwise-not of in plus 1 (two's complement).
    check_twos_complement_equivalence: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        out == (~in + 4'd1)
    );

    // The 4-bit sum of in and out wraps to zero (modulo-16).
    check_sum_wraps_to_zero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in + out) == 4'd0
    );

    // Two's complement is involutive: complement of out == in.
    check_involution: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        ((~out) + 4'd1) == in
    );

    ///// Corner cases /////
    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd0) |-> (out == 4'd0)
    );

    // If out is zero, input must have been zero.
    check_only_zero_maps_to_zero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (out == 4'd0) |-> (in == 4'd0)
    );

    // Minimum 4-bit two's-complement value (8) maps to itself.
    check_min_neg_self_inverse: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'h8) |-> (out == 4'h8)
    );

    // out equals in only for fixed points 0 or 8.
    check_only_fixed_points_equal: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (out == in) |-> ((in == 4'h0) || (in == 4'h8))
    );
endmodule