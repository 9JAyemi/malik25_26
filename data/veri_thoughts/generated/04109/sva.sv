module multiplier_sva #(
    parameter int n = 8,
    parameter int signed_mode = 1
) (
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic [n-1:0] result
);

    generate
        if (signed_mode == 1) begin : gen_signed_mode
            // Signed mode uses the low n bits of the sign-extended product.
            check_signed_mode_result: assert property (
                @(posedge clk)
                result == (({a[n-1], {n-1{a[n-1]}}, a} * {b[n-1], {n-1{b[n-1]}}, b}) & {n{1'b1}})
            );
        end else begin : gen_unsigned_mode
            // Unsigned mode uses the low n bits of the direct product.
            check_unsigned_mode_result: assert property (
                @(posedge clk)
                result == ((a * b) & {n{1'b1}})
            );
        end
    endgenerate

    // The observable result matches the low n bits of a*b.
    check_result_matches_low_product: assert property (
        @(posedge clk)
        result == ((a * b) & {n{1'b1}})
    );

    // Zero on a forces a zero result.
    check_zero_a: assert property (
        @(posedge clk)
        (a == '0) |-> (result == '0)
    );

    // Zero on b forces a zero result.
    check_zero_b: assert property (
        @(posedge clk)
        (b == '0) |-> (result == '0)
    );

    // Multiplying by one on b returns a.
    check_one_on_b: assert property (
        @(posedge clk)
        (b == {{n-1{1'b0}}, 1'b1}) |-> (result == a)
    );

    // Multiplying by one on a returns b.
    check_one_on_a: assert property (
        @(posedge clk)
        (a == {{n-1{1'b0}}, 1'b1}) |-> (result == b)
    );

    // The product LSB is the AND of the operand LSBs.
    check_lsb_product_rule: assert property (
        @(posedge clk)
        result[0] == (a[0] & b[0])
    );

    // Stable sampled inputs keep the sampled result stable.
    check_stable_inputs_keep_result_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable(a) && $stable(b)) |-> $stable(result)
    );

    // A sampled result change requires a sampled input change.
    check_result_change_requires_input_change: assert property (
        @(posedge clk)
        (!$initstate && !$stable(result)) |-> (!$stable(a) || !$stable(b))
    );

endmodule