module full_adder_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic a,
    input  logic b,
    input  logic cin,
    input  logic cout,
    input  logic sum
);
    // Sum equals a ^ b ^ cin.
    check_sum_xor3: assert property (
        @(posedge CLK) disable iff (!RESETn)
        sum == (a ^ b ^ cin)
    );

    // Carry-out equals (a & b) | ((a ^ b) & cin).
    check_cout_logic: assert property (
        @(posedge CLK) disable iff (!RESETn)
        cout == ((a & b) | ((a ^ b) & cin))
    );

    // With cin=0, sum equals a ^ b.
    check_sum_when_cin0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (cin == 1'b0) |-> (sum == (a ^ b))
    );

    // With cin=0, carry equals a & b.
    check_cout_when_cin0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (cin == 1'b0) |-> (cout == (a & b))
    );

    // With cin=1, sum equals ~(a ^ b).
    check_sum_when_cin1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (cin == 1'b1) |-> (sum == ~(a ^ b))
    );

    // With cin=1, carry equals (a & b) | (a ^ b).
    check_cout_when_cin1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (cin == 1'b1) |-> (cout == ((a & b) | (a ^ b)))
    );

    // If a & b is 1, carry must be 1.
    check_carry_when_ab: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (a & b) |-> (cout == 1'b1)
    );

    // If cin=1 and a ^ b = 1, carry must be 1.
    check_carry_when_cin_and_axorb: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((cin == 1'b1) && (a ^ b)) |-> (cout == 1'b1)
    );

    // When neither a&b nor (a^b)&cin is 1, carry must be 0.
    check_no_carry_sources: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (!((a & b) | ((a ^ b) & cin))) |-> (cout == 1'b0)
    );

    // All-low inputs produce sum=0 and cout=0.
    check_all_zero_case: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((!a) && (!b) && (!cin)) |-> ((sum == 1'b0) && (cout == 1'b0))
    );

    // All-high inputs produce sum=1 and cout=1.
    check_all_one_case: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (a && b && cin) |-> ((sum == 1'b1) && (cout == 1'b1))
    );
endmodule