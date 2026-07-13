module full_adder_sva (
    input logic CLK,
    input logic RESETn,
    input logic a,
    input logic b,
    input logic cin,
    input logic sum,
    input logic carry
);
    // Combinational full_adder; sample properties on external CLK, gated by active-low RESETn.

    // Sum equals a ^ b ^ cin.
    check_sum_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) sum == ((a ^ b) ^ cin)
    );

    // Carry equals (a & b) | ((a ^ b) & cin).
    check_carry_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) carry == ((a & b) | ((a ^ b) & cin))
    );

    // Carry equals majority form: (a&b) | (a&cin) | (b&cin).
    check_carry_majority_form: assert property (
        @(posedge CLK) disable iff (!RESETn) carry == ((a & b) | (a & cin) | (b & cin))
    );

    // With cin=0, sum reduces to a ^ b.
    check_sum_when_cin0: assert property (
        @(posedge CLK) disable iff (!RESETn) (cin == 1'b0) |-> (sum == (a ^ b))
    );

    // With cin=0, carry reduces to a & b.
    check_carry_when_cin0: assert property (
        @(posedge CLK) disable iff (!RESETn) (cin == 1'b0) |-> (carry == (a & b))
    );

    // With cin=1, sum equals ~(a ^ b).
    check_sum_when_cin1: assert property (
        @(posedge CLK) disable iff (!RESETn) (cin == 1'b1) |-> (sum == ~(a ^ b))
    );

    // With cin=1, carry equals a | b.
    check_carry_when_cin1: assert property (
        @(posedge CLK) disable iff (!RESETn) (cin == 1'b1) |-> (carry == (a | b))
    );

    // When a and b differ, carry equals cin.
    check_carry_equals_cin_when_inputs_differ: assert property (
        @(posedge CLK) disable iff (!RESETn) ((a ^ b) == 1'b1) |-> (carry == cin)
    );

    // When a and b are equal, sum equals cin.
    check_sum_equals_cin_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) ((a ^ b) == 1'b0) |-> (sum == cin)
    );

    // With all ones, sum=1 and carry=1.
    check_all_one_input_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (a & b & cin) |-> ((sum == 1'b1) && (carry == 1'b1))
    );
endmodule