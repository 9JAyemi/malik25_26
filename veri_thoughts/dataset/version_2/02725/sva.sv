module binary_addition_sva (
    input  logic CLK,          // External sampling clock for SVA
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] sum
);
    // Sum equals 8-bit addition of a and b (modulo 256).
    check_sum_is_add: assert property (
        @(posedge CLK) sum == (a + b)
    );

    // If a is zero, sum equals b.
    check_zero_a_identity: assert property (
        @(posedge CLK) (a == 8'h00) |-> (sum == b)
    );

    // If b is zero, sum equals a.
    check_zero_b_identity: assert property (
        @(posedge CLK) (b == 8'h00) |-> (sum == a)
    );

    // Subtracting b from sum recovers a (modulo 256).
    check_subtract_recovers_a: assert property (
        @(posedge CLK) (sum - b) == a
    );

    // Subtracting a from sum recovers b (modulo 256).
    check_subtract_recovers_b: assert property (
        @(posedge CLK) (sum - a) == b
    );

    // If inputs are stable across a cycle, sum is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // Specific wrap-around example: 0xFF + 0x01 -> 0x00.
    check_wrap_example_ff_plus_01: assert property (
        @(posedge CLK) ((a == 8'hFF) && (b == 8'h01)) |-> (sum == 8'h00)
    );
endmodule