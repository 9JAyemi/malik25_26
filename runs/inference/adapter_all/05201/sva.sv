module binary_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       En,
    input logic [3:0] S,
    input logic       Cout
);

    // S is zero when the enable is low.
    check_s_zero_when_disabled: assert property (
        @(posedge clk) !En |-> (S == 4'b0000)
    );

    // S is the 4-bit sum when the enable is high.
    check_s_sum_when_enabled: assert property (
        @(posedge clk) En |-> (S == (A + B + Cin))
    );

    // Cout is always low in this RTL.
    check_cout_always_low: assert property (
        @(posedge clk) Cout == 1'b0
    );

    // The full output vector matches the enabled sum and zero carry.
    check_full_output_when_enabled: assert property (
        @(posedge clk) En |-> ({Cout, S} == {1'b0, (A + B + Cin)})
    );

    // The disabled output vector is zero.
    check_full_output_when_disabled: assert property (
        @(posedge clk) !En |-> ({Cout, S} == 5'b00000)
    );

endmodule