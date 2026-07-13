module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       En,
    input logic [3:0] S,
    input logic       Cout
);

    // When enabled, S reflects the 4-bit sum of A, B, and Cin.
    check_sum_when_enabled: assert property (
        @(posedge $global_clock) En |-> (S == (A + B + Cin))
    );

    // When disabled, S is forced to zero.
    check_zero_when_disabled: assert property (
        @(posedge $global_clock) !En |-> (S == 4'b0000)
    );

    // S always matches the enable-controlled sum output.
    check_output_mux_behavior: assert property (
        @(posedge $global_clock) S == (En ? (A + B + Cin) : 4'b0000)
    );

    // Cout is always low in this implementation.
    check_cout_constant_low: assert property (
        @(posedge $global_clock) Cout == 1'b0
    );

endmodule