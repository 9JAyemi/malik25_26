module full_adder_csa_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum
);

    // Carry-out is the majority function of a, b, and cin.
    check_cout_majority: assert property (
        @(posedge clk)
        cout == ((a & b) | (a & cin) | (b & cin))
    );

    // Sum matches the combinational function implemented by the RTL.
    check_sum_function: assert property (
        @(posedge clk)
        sum == (cin ? ~(a ^ b) : (a | b))
    );

    // With cin low, sum becomes OR and carry becomes AND of a and b.
    check_cin_low_behavior: assert property (
        @(posedge clk)
        !cin |-> ((sum == (a | b)) && (cout == (a & b)))
    );

    // With cin high, sum becomes XNOR and carry becomes OR of a and b.
    check_cin_high_behavior: assert property (
        @(posedge clk)
        cin |-> ((sum == ~(a ^ b)) && (cout == (a | b)))
    );

    // When both data inputs are low, carry is low and sum follows cin.
    check_ab_zero_behavior: assert property (
        @(posedge clk)
        (!a && !b) |-> ((!cout) && (sum == cin))
    );

    // When the data inputs differ, carry follows cin and sum inverts cin.
    check_ab_different_behavior: assert property (
        @(posedge clk)
        (a ^ b) |-> ((cout == cin) && (sum == ~cin))
    );

    // When both data inputs are high, both outputs are high.
    check_ab_one_behavior: assert property (
        @(posedge clk)
        (a && b) |-> (cout && sum)
    );

endmodule