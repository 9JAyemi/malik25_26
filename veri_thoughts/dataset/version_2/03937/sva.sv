module calculator_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        reset_n,
    input logic [31:0] add,
    input logic [31:0] sub,
    input logic [31:0] mul,
    input logic [31:0] div
);

    // External sampling clock; DUT logic is combinational with active-low reset_n.

    // Active-low reset forces all outputs to zero.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        (!reset_n) |-> ((add == 32'd0) && (sub == 32'd0) && (mul == 32'd0) && (div == 32'd0))
    );

    // add must match the sum of a and b outside reset.
    check_add_matches_sum: assert property (
        @(posedge clk) disable iff (!reset_n)
        (add == (a + b))
    );

    // sub must match the difference of a and b outside reset.
    check_sub_matches_difference: assert property (
        @(posedge clk) disable iff (!reset_n)
        (sub == (a - b))
    );

    // mul must match the low 32 bits of the product outside reset.
    check_mul_matches_product: assert property (
        @(posedge clk) disable iff (!reset_n)
        (mul == ((a * b) & 64'h0000_0000_FFFF_FFFF))
    );

    // div must match a / b when the divisor is nonzero.
    check_div_matches_quotient: assert property (
        @(posedge clk) disable iff (!reset_n)
        (b != 32'd0) |-> (div == (a / b))
    );

    // div must be zero when the divisor is zero.
    check_div_zero_on_zero_divisor: assert property (
        @(posedge clk) disable iff (!reset_n)
        (b == 32'd0) |-> (div == 32'd0)
    );

    // Stable inputs keep all outputs stable outside reset.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($stable({a, b})) |-> ($stable({add, sub, mul, div}))
    );

endmodule