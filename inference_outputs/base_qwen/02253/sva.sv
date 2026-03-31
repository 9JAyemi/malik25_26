```systemverilog
module alu_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    output logic [3:0] out
);
    // Combinational logic, so use @(posedge clk)
    // Addition operation
    addition_check: assert property (
        @(posedge clk) $rose(op == 3'b000) |-> (out == a + b)
    );
    // Subtraction operation
    subtraction_check: assert property (
        @(posedge clk) $rose(op == 3'b001) |-> (out == a - b)
    );
    // Bitwise AND operation
    and_check: assert property (
        @(posedge clk) $rose(op == 3'b010) |-> (out == a & b)
    );
    // Bitwise OR operation
    or_check: assert property (
        @(posedge clk) $rose(op == 3'b011) |-> (out == a | b)
    );
    // Bitwise XOR operation
    xor_check: assert property (
        @(posedge clk) $rose(op == 3'b100) |-> (out == a ^ b)
    );
    // Shift left operation
    shift_left_check: assert property (
        @(posedge clk) $rose(op == 3'b101) |-> (out == {a[2:0], 1'b0})
    );
    // Default to 0 for undefined operations
    default_check: assert property (
        @(posedge clk) $rose(op != 3'b000 && op != 3'b001 && op != 3'b010 && op != 3'b011 && op != 3'b100 && op != 3'b101) |-> (out == 4'b0)
    );
endmodule
```