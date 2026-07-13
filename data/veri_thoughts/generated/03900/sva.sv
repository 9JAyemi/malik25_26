module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic en,
    input logic [3:0] sum,
    input logic carry
);

    // Outputs are forced low when enable is deasserted.
    check_outputs_zero_when_disabled: assert property (
        @(posedge clk) !en |-> (sum == 4'b0000 && carry == 1'b0)
    );

    // Sum matches the 4-bit addition when enable is asserted.
    check_sum_matches_addition_when_enabled: assert property (
        @(posedge clk) en |-> (sum == (a + b))
    );

    // Carry matches the implemented masked MSB behavior when enabled.
    check_carry_matches_a_msb_when_enabled: assert property (
        @(posedge clk) en |-> (carry == a[3])
    );

    // Sum always follows the enable-gated combinational equation.
    check_sum_function: assert property (
        @(posedge clk) sum == (en ? (a + b) : 4'b0000)
    );

    // Carry always follows the enable-gated combinational equation.
    check_carry_function: assert property (
        @(posedge clk) carry == (en ? a[3] : 1'b0)
    );

endmodule