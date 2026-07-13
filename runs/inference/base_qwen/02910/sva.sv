module top_module_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] sum
);
    // Combinational logic, so use @(posedge CLK)
    // Check that the sum is correctly calculated
    check_sum: assert property (
        @(posedge CLK) $rose(sum) |-> (sum == a + b)
    ) else $error("Sum calculation is incorrect");

    // Check that the carry select adder correctly handles carry propagation
    check_carry_propagation: assert property (
        @(posedge CLK) $rose(sum) |-> (sum[31] == (a[31] + b[31] + (a[15] + b[15] >= 16'b10000)))
    ) else $error("Carry propagation is incorrect");

    // Check that the lower half adder correctly calculates the lower 16 bits
    check_lower_half_adder: assert property (
        @(posedge CLK) $rose(sum) |-> (sum[15:0] == a[15:0] + b[15:0])
    ) else $error("Lower half adder calculation is incorrect");

    // Check that the upper half adder correctly calculates the upper 16 bits without carry
    check_upper_half_adder_cin0: assert property (
        @(posedge CLK) $rose(sum) |-> (sum[31:16] == a[31:16] + b[31:16])
    ) else $error("Upper half adder calculation without carry is incorrect");

    // Check that the upper half adder correctly calculates the upper 16 bits with carry
    check_upper_half_adder_cin1: assert property (
        @(posedge CLK) $rose(sum) |-> (sum[31:16] == a[31:16] + b[31:16] + 16'b1)
    ) else $error("Upper half adder calculation with carry is incorrect");

    // Check that the carry select adder correctly selects the correct upper half sum
    check_carry_select_adder: assert property (
        @(posedge CLK) $rose(sum) |-> (sum[31:16] == (a[15] + b[15] >= 16'b10000) ? a[31:16] + b[31:16] + 16'b1 : a[31:16] + b[31:16])
    ) else $error("Carry select adder selection is incorrect");
endmodule