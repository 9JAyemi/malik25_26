module add_subtract_sva (
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic        sel,
    input  logic [7:0]  result
);
    // Result matches selected add/sub operation.
    check_result_muxed_operation: assert property (
        @(posedge CLK) disable iff (!RESETn) result == (sel ? (a - b) : (a + b))
    );

    // When sel=0, result equals a+b.
    check_add_result: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel) |-> (result == (a + b))
    );

    // When sel=1, result equals a-b.
    check_sub_result: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel) |-> (result == (a - b))
    );

    // For sel=0, commutativity holds: result == b+a.
    check_add_commutative: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel) |-> (result == (b + a))
    );

    // For sel=1, inverse identity: (result + b) == a (mod 256).
    check_sub_inverse_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel) |-> ((result + b) == a)
    );

    // For sel=0, inverse identity: (result - b) == a (mod 256).
    check_add_inverse_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel) |-> ((result - b) == a)
    );

    // If b==0, result equals a for both operations.
    check_b_zero_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (b == 8'h00) |-> (result == a)
    );

    // If sel=0 and a==0, result equals b.
    check_a_zero_add_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel && (a == 8'h00)) |-> (result == b)
    );

    // If sel=1 and a==0, result equals (0 - b) (two's complement).
    check_a_zero_sub_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel && (a == 8'h00)) |-> (result == (8'h00 - b))
    );

    // If inputs are stable across a cycle, result must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({a,b,sel}) |-> $stable(result)
    );
endmodule