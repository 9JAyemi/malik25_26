module half_full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic s,
    input logic cout
);

    // DUT is combinational; clk is only used for assertion sampling.

    // Sum matches the XOR of all three inputs.
    check_sum_function: assert property (
        @(posedge clk) s === (a ^ b ^ cin)
    );

    // Carry-out matches the implemented full-adder carry equation.
    check_cout_function: assert property (
        @(posedge clk) cout === (((a ^ b) & cin) | (a & b))
    );

    // With cin low, sum reduces to the half-adder sum of a and b.
    check_half_adder_sum_when_cin_low: assert property (
        @(posedge clk) !cin |-> (s === (a ^ b))
    );

    // With cin low, carry reduces to the half-adder carry of a and b.
    check_half_adder_carry_when_cin_low: assert property (
        @(posedge clk) !cin |-> (cout === (a & b))
    );

    // With cin high, sum is the inverse of a XOR b.
    check_sum_when_cin_high: assert property (
        @(posedge clk) cin |-> (s === ~(a ^ b))
    );

    // With cin high, carry-out is the OR of a and b.
    check_carry_when_cin_high: assert property (
        @(posedge clk) cin |-> (cout === (a | b))
    );

    // When a and b are equal, the sum output follows cin.
    check_sum_when_inputs_equal: assert property (
        @(posedge clk) (a == b) |-> (s === cin)
    );

    // When a and b differ, the carry output follows cin.
    check_carry_when_inputs_differ: assert property (
        @(posedge clk) (a != b) |-> (cout === cin)
    );

endmodule