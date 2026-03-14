module pipelined_multiplier_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        enable,
    input logic [31:0] result
);
    ///// Functional transform on enable posedge /////
    // On each enable edge, next-sampled result equals (a[15:0]*b[15:0]) + ((a[31:16]*b[31:16]) << 16) from that edge.
    check_result_next_equals_split_sum: assert property (
        @(posedge enable) 1'b1 |=> result == $past( ( (a[15:0] * b[15:0]) + ((a[31:16] * b[31:16]) << 16) ) )
    );

    // On each enable edge, next-sampled result[15:0] equals low 16 bits of (a[15:0]*b[15:0]) from that edge.
    check_lower16_matches_ll_product: assert property (
        @(posedge enable) 1'b1 |=> result[15:0] == $past( (a[15:0] * b[15:0]) [15:0] )
    );

    // On each enable edge, next-sampled result[31:16] equals ((a[15:0]*b[15:0])>>16 + (a[31:16]*b[31:16])[15:0]) low 16 bits from that edge.
    check_upper16_matches_composed_sum: assert property (
        @(posedge enable) 1'b1 |=> result[31:16] == $past( ( ( ( (a[15:0] * b[15:0]) >> 16 ) [15:0] ) + ( (a[31:16] * b[31:16]) [15:0] ) ) [15:0] )
    );

    ///// Stability properties /////
    // If a and b are unchanged across consecutive enable edges, result is unchanged at the next edge.
    check_result_stable_if_inputs_stable: assert property (
        @(posedge enable) (a == $past(a) && b == $past(b)) |=> (result == $past(result))
    );

    // If only low halves of a and b are unchanged across edges, result[15:0] is unchanged at the next edge.
    check_low16_stable_if_low_inputs_stable: assert property (
        @(posedge enable) ((a[15:0] == $past(a[15:0])) && (b[15:0] == $past(b[15:0]))) |=> (result[15:0] == $past(result[15:0]))
    );

    ///// Special-case input patterns /////
    // If either operand is zero at an enable edge, result becomes zero at the next edge.
    check_result_zero_when_operand_zero: assert property (
        @(posedge enable) ((a == 32'd0) || (b == 32'd0)) |=> (result == 32'd0)
    );

    // If both high halves are zero at an enable edge, next-sampled result equals (a[15:0]*b[15:0]).
    check_result_equals_ll_when_high_zero: assert property (
        @(posedge enable) ((a[31:16] == 16'd0) && (b[31:16] == 16'd0)) |=> (result == $past(a[15:0] * b[15:0]))
    );

    // If any low half is zero at an enable edge, next-sampled result[15:0] is zero.
    check_low16_zero_when_any_low_zero: assert property (
        @(posedge enable) ((a[15:0] == 16'd0) || (b[15:0] == 16'd0)) |=> (result[15:0] == 16'd0)
    );

    // If any low half is zero at an enable edge, next-sampled result[31:16] equals (a[31:16]*b[31:16])[15:0].
    check_upper16_eq_msbprod_low16_when_low_zero: assert property (
        @(posedge enable) ((a[15:0] == 16'd0) || (b[15:0] == 16'd0)) |=> (result[31:16] == $past( (a[31:16] * b[31:16]) [15:0] ))
    );
endmodule