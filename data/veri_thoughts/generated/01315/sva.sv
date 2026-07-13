module or_32_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out
);
    // Note: DUT has no clock/reset; assertions sample on external clk with active-low reset.

    // Out must equal bitwise OR of inputs.
    check_vector_or_equivalence: assert property (
        @(posedge clk) disable iff (!rst_n) out == (a | b)
    );

    // If both inputs are zero, output must be zero.
    check_zero_inputs_zero_output: assert property (
        @(posedge clk) disable iff (!rst_n) ((a == 32'b0) && (b == 32'b0)) |-> (out == 32'b0)
    );

    // When a is zero, out must equal b.
    check_pass_through_when_a_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (a == 32'b0) |-> (out == b)
    );

    // When b is zero, out must equal a.
    check_pass_through_when_b_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (b == 32'b0) |-> (out == a)
    );

    // When a equals b, out must equal a (idempotent OR).
    check_idempotent_when_inputs_equal: assert property (
        @(posedge clk) disable iff (!rst_n) (a == b) |-> (out == a)
    );

    // Out cannot have 1s where both inputs are 0.
    check_out_subset_of_or_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) ((out & ~(a | b)) == 32'b0)
    );

    // Any input 1s must appear in out.
    check_inputs_cover_output: assert property (
        @(posedge clk) disable iff (!rst_n) (((a | b) & ~out) == 32'b0)
    );

    genvar i;
    for (i = 0; i < 32; i++) begin : bit_edge_checks
        // A rising edge on out[i] must be caused by a rise on a[i] or b[i].
        check_out_rise_has_input_rise: assert property (
            @(posedge clk) disable iff (!rst_n) $rose(out[i]) |-> ($rose(a[i]) || $rose(b[i]))
        );
        // A falling edge on out[i] must be caused by a fall on a[i] or b[i].
        check_out_fall_has_input_fall: assert property (
            @(posedge clk) disable iff (!rst_n) $fell(out[i]) |-> ($fell(a[i]) || $fell(b[i]))
        );
    end

endmodule