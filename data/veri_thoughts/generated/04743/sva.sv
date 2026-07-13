module ripple_carry_adder_sva #(parameter int n = 4) (
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic cin,
    input logic [n-1:0] s,
    input logic cout
);

    genvar i;

    // Full result matches n-bit addition with carry in.
    check_full_result_matches_addition: assert property (
        @(posedge clk) {cout, s} == ({1'b0, a} + {1'b0, b} + cin)
    );

    generate
        if (n > 0) begin : gen_adder_checks
            // Least significant sum bit matches the first full-adder stage.
            check_lsb_sum_matches_xor: assert property (
                @(posedge clk) s[0] == (a[0] ^ b[0] ^ cin)
            );

            for (i = 1; i < n; i = i + 1) begin : gen_prefix_checks
                // Lower sum bits match addition of the corresponding input prefixes.
                check_lower_bits_match_prefix_add: assert property (
                    @(posedge clk) s[i:0] == (({1'b0, a[i:0]} + {1'b0, b[i:0]} + cin)[i:0])
                );
            end
        end
    endgenerate

    // Zero operands and zero carry-in produce zero outputs.
    check_zero_inputs_produce_zero_outputs: assert property (
        @(posedge clk) (a == '0 && b == '0 && cin == 1'b0) |-> (s == '0 && cout == 1'b0)
    );

    // With b and carry-in low, the output equals a.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @(posedge clk) (b == '0 && cin == 1'b0) |-> (s == a && cout == 1'b0)
    );

    // With a and carry-in low, the output equals b.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @(posedge clk) (a == '0 && cin == 1'b0) |-> (s == b && cout == 1'b0)
    );

    // Incrementing an all-ones input wraps the sum and raises carry-out.
    check_all_ones_plus_cin_wraps_with_carry: assert property (
        @(posedge clk) (a == {n{1'b1}} && b == '0 && cin == 1'b1) |-> (s == '0 && cout == 1'b1)
    );

endmodule