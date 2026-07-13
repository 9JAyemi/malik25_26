module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic En,
    input logic [3:0] S,
    input logic Cout
);

// When enabled, S matches the 4-bit sum of A, B, and Cin.
    check_enabled_sum: assert property (
        @(posedge clk) En |-> (S == (A + B + Cin))
    );

// When disabled, S is zero.
    check_disabled_zero: assert property (
        @(posedge clk) !En |-> (S == 4'b0000)
    );

// When enabled, Cout matches the carry out of the 4-bit sum.
    check_enabled_cout: assert property (
        @(posedge clk) En |-> (Cout == ((A + B + Cin) >= 5'd16))
    );

// When disabled, Cout is low.
    check_disabled_cout_low: assert property (
        @(posedge clk) !En |-> (Cout == 1'b0)
    );

// With B and Cin low, S passes A when enabled.
    check_a_passthrough_when_b0_cin0: assert property (
        @(posedge clk) (!En || (B == 4'b0000 && Cin == 1'b0)) |-> (S == (En ? A : 4'b0000))
    );

// With A and Cin low, S passes B when enabled.
    check_b_passthrough_when_a0_cin0: assert property (
        @(posedge clk) (!En || (A == 4'b0000 && Cin == 1'b0)) |-> (S == (En ? B : 4'b0000))
    );

// With A and B low, S equals Cin when enabled.
    check_cin_passthrough_when_a0_b0: assert property (
        @(posedge clk) (!En || (A == 4'b0000 && B == 4'b0000)) |-> (S == (En ? Cin : 4'b0000))
    );

// With A and B equal to Cin, S is all ones when enabled.
    check_all_ones_when_equal_inputs: assert property (
        @(posedge clk) (!En || (A == B && B == Cin)) |-> (S == 4'b1111)
    );

// With A and B equal to Cin, Cout is high when enabled.
    check_cout_high_when_equal_inputs: assert property (
        @(posedge clk) (!En || (A == B && B == Cin)) |-> (Cout == 1'b1)
    );

endmodule
