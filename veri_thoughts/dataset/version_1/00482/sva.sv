module binary_multiplier_assertions (
    input logic        clk,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic [7:0]  out
);

    // out matches the implemented combinational expression.
    check_out_matches_implemented_function: assert property (
        @(posedge clk) out == {(a[2] & b), (a[3] & b)}
    );

    // The upper nibble is b masked by a[2].
    check_upper_nibble_matches_a2_mask: assert property (
        @(posedge clk) out[7:4] == (a[2] & b)
    );

    // The lower nibble is b masked by a[3].
    check_lower_nibble_matches_a3_mask: assert property (
        @(posedge clk) out[3:0] == (a[3] & b)
    );

    // Zero on b forces the full output low.
    check_zero_output_when_b_zero: assert property (
        @(posedge clk) (b == 4'h0) |-> (out == 8'h00)
    );

    // Zero on a[3:2] forces the full output low.
    check_zero_output_when_a23_zero: assert property (
        @(posedge clk) (a[3:2] == 2'b00) |-> (out == 8'h00)
    );

    // Changes on a[1:0] alone do not affect the output.
    check_output_ignores_a10_changes: assert property (
        @(posedge clk) ($stable(b) && $stable(a[3:2]) && $changed(a[1:0])) |-> $stable(out)
    );

    // The upper nibble does not depend on a[3].
    check_upper_nibble_independent_of_a3: assert property (
        @(posedge clk) ($stable(b) && $stable(a[2]) && $changed(a[3])) |-> $stable(out[7:4])
    );

    // The lower nibble does not depend on a[2].
    check_lower_nibble_independent_of_a2: assert property (
        @(posedge clk) ($stable(b) && $stable(a[3]) && $changed(a[2])) |-> $stable(out[3:0])
    );

endmodule