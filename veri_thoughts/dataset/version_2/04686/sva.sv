module adder_4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Output concatenation matches the RTL adder expression.
    check_full_add_result: assert property (
        @(posedge clk) {cout, sum} == (cin + a + b)
    );

    // Zero inputs produce a zero result.
    check_zero_inputs: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == 5'b00000)
    );

    // Adding zero with cin low passes a through unchanged.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @(posedge clk) ((b == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero with cin low passes b through unchanged.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @(posedge clk) ((a == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == {1'b0, b})
    );

    // With only cin asserted, the result is one.
    check_cin_only_result: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000) && (cin == 1'b1)) |-> ({cout, sum} == 5'b00001)
    );

    // Unchanged inputs imply unchanged outputs for this combinational adder.
    check_stable_inputs_imply_stable_outputs: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({cout, sum})
    );

endmodule