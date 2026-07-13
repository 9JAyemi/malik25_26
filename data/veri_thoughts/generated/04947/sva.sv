module adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Combined output must equal the RTL addition result.
    check_full_add_result: assert property (
        @(posedge clk) {cout, sum} == (a + b + cin)
    );

    // Zero inputs must produce a zero result.
    check_zero_addition: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == 5'b00000)
    );

    // Adding zero with no carry-in must pass through a.
    check_passthrough_a: assert property (
        @(posedge clk) ((b == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero with no carry-in must pass through b.
    check_passthrough_b: assert property (
        @(posedge clk) ((a == 4'b0000) && (cin == 1'b0)) |-> ({cout, sum} == {1'b0, b})
    );

    // Maximum inputs with carry-in must produce the full 5-bit maximum sum.
    check_max_addition: assert property (
        @(posedge clk) ((a == 4'hf) && (b == 4'hf) && (cin == 1'b1)) |-> ({cout, sum} == 5'h1f)
    );

    // Stable inputs across samples must keep outputs stable.
    check_stable_inputs_imply_stable_outputs: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({cout, sum})
    );

endmodule