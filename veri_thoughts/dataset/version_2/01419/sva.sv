module ripple_carry_adder_sva #(
    parameter int WIDTH = 4
) (
    input logic clk,
    // DUT ports
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic              cin,
    input logic [WIDTH-1:0] sum,
    input logic              cout
);
    localparam [WIDTH-1:0] ZEROS = {WIDTH{1'b0}};
    localparam [WIDTH-1:0] ONES  = {WIDTH{1'b1}};

    ///// Functional correctness /////
    // Outputs implement {cout,sum} == a + b + cin (zero-extended).
    check_adder_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
            {cout, sum} == ({1'b0, a} + {1'b0, b} + {{WIDTH{1'b0}}, cin})
    );

    // LSB sum equals XOR of a[0], b[0], and cin.
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (1'b0)
            sum[0] == (a[0] ^ b[0] ^ cin)
    );

    ///// Simple corner cases /////
    // 0 + 0 + 0 => sum=0, cout=0.
    check_zero_plus_zero_cin0: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == ZEROS) && (b == ZEROS) && (cin == 1'b0) |-> (sum == ZEROS) && (cout == 1'b0)
    );

    // 0 + 0 + 1 => sum=1, cout=0.
    check_zero_plus_zero_cin1: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == ZEROS) && (b == ZEROS) && (cin == 1'b1) |-> (sum == {{(WIDTH-1){1'b0}}, 1'b1}) && (cout == 1'b0)
    );

    // a + 0 + 0 => sum=a, cout=0.
    check_b_zero_cin0_passthru_a: assert property (
        @(posedge clk) disable iff (1'b0)
            (b == ZEROS) && (cin == 1'b0) |-> (sum == a) && (cout == 1'b0)
    );

    // 0 + b + 0 => sum=b, cout=0.
    check_a_zero_cin0_passthru_b: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == ZEROS) && (cin == 1'b0) |-> (sum == b) && (cout == 1'b0)
    );

    // (all 1s) + 0 + 1 => sum=0, cout=1.
    check_allones_plus_one: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == ONES) && (b == ZEROS) && (cin == 1'b1) |-> (sum == ZEROS) && (cout == 1'b1)
    );

    // (all 1s) + (all 1s) + 1 => sum=all 1s, cout=1.
    check_allones_plus_allones_plus_one: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == ONES) && (b == ONES) && (cin == 1'b1) |-> (sum == ONES) && (cout == 1'b1)
    );

    ///// Relational properties /////
    // Swapping a and b across cycles preserves outputs (commutativity).
    check_commutativity_swap_invariance: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == $past(b)) && (b == $past(a)) && (cin == $past(cin)) |-> (sum == $past(sum)) && (cout == $past(cout))
    );

    // If inputs are stable, outputs remain stable (purely combinational).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
            $stable(a) && $stable(b) && $stable(cin) |-> $stable(sum) && $stable(cout)
    );
endmodule