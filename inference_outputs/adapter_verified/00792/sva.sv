module xor_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb_logic
);

// Output equals a ^ b on a rising edge.
    check_xor_on_a: assert property (
        @(posedge clk) out_comb_logic == (a ^ b)
    );

// Output equals a ^ b on a falling edge.
    check_xor_on_a_fall: assert property (
        @(negedge clk) out_comb_logic == (a ^ b)
    );

// Output equals a ^ b on b rising edge.
    check_xor_on_b: assert property (
        @(posedge clk) out_comb_logic == (a ^ b)
    );

// Output equals a ^ b on b falling edge.
    check_xor_on_b_fall: assert property (
        @(negedge clk) out_comb_logic == (a ^ b)
    );

// When a==b, out_comb_logic is 0 on a rising edge.
    check_zero_when_equal_a: assert property (
        @(posedge clk) (a == b) |-> (out_comb_logic == 1'b0)
    );

// When a==b, out_comb_logic is 0 on a falling edge.
    check_zero_when_equal_a_fall: assert property (
        @(negedge clk) (a == b) |-> (out_comb_logic == 1'b0)
    );

// When a!=b, out_comb_logic is 1 on a rising edge.
    check_one_when_not_equal_a: assert property (
        @(posedge clk) (a != b) |-> (out_comb_logic == 1'b1)
    );

// When a!=b, out_comb_logic is 1 on a falling edge.
    check_one_when_not_equal_a_fall: assert property (
        @(negedge clk) (a != b) |-> (out_comb_logic == 1'b1)
    );

endmodule
