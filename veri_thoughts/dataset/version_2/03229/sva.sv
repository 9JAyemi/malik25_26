module full_adder_assertions (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum
);

    // sum matches the chained XOR implementation.
    check_sum_xor_chain: assert property (
        @(posedge clk) (sum === (a ^ b ^ cin))
    );

    // cout is high only when cin is high and a/b differ.
    check_cout_xor_and_cin: assert property (
        @(posedge clk) (cout === ((a ^ b) & cin))
    );

    // With cin low, sum is a^b and cout stays low.
    check_cin_low_behavior: assert property (
        @(posedge clk) (!cin) |-> ((sum === (a ^ b)) && (cout === 1'b0))
    );

    // With cin high, sum inverts a^b and cout mirrors a^b.
    check_cin_high_behavior: assert property (
        @(posedge clk) (cin) |-> ((sum === ~(a ^ b)) && (cout === (a ^ b)))
    );

    // Equal a/b inputs make sum follow cin and force cout low.
    check_equal_ab_behavior: assert property (
        @(posedge clk) (!(a ^ b)) |-> ((sum === cin) && (cout === 1'b0))
    );

    // Different a/b inputs make sum invert cin and cout follow cin.
    check_unequal_ab_behavior: assert property (
        @(posedge clk) (a ^ b) |-> ((sum === ~cin) && (cout === cin))
    );

endmodule