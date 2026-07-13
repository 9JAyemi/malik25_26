module ripple_carry_adder_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] sum
);
    // Full adder sum calculation
    full_adder_sum: assert property (
        @(posedge clk) disable iff (!reset_n) sum == (a + b)
    );

    // Full adder carry calculation
    full_adder_carry: assert property (
        @(posedge clk) disable iff (!reset_n) sum[8] == (a[7] & b[7]) | (a[7] & carry[7]) | (b[7] & carry[7])
    );

    // Ripple carry calculation
    ripple_carry: assert property (
        @(posedge clk) disable iff (!reset_n) sum[8] == carry[8]
    );

    // Carry propagation through full adders
    carry_propagation: assert property (
        @(posedge clk) disable iff (!reset_n) $forall (i = 0 to 7) (carry[i + 1] == (a[i] & b[i]) | (a[i] & carry[i]) | (b[i] & carry[i]))
    );

    // Sum calculation for each bit
    sum_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) $forall (i = 0 to 7) (sum[i] == a[i] ^ b[i] ^ carry[i])
    );

    // Reset behavior
    reset_behavior: assert property (
        @(posedge clk) !reset_n |-> (sum == 8'b0)
    );
endmodule