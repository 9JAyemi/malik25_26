```systemverilog
module adder_subtractor_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    output logic [3:0] result,
    output logic OVFL
);
    // Combinational logic, so use @(posedge clk)
    // Check that the result is correctly calculated based on the SUB signal
    check_result: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 1) |-> (result == A - B)
    );
    check_result_add: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 0) |-> (result == A + B)
    );
    // Check that the overflow flag is set correctly
    check_overflow: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 1) |-> (result[3] == 1) |-> (OVFL == 1)
    );
    check_overflow_add: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 0) |-> (result[3] == 1) |-> (OVFL == 1)
    );
    // Check that the overflow flag is not set when there is no overflow
    check_no_overflow: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 1) |-> (result[3] == 0) |-> (OVFL == 0)
    );
    check_no_overflow_add: assert property (
        @(posedge clk) disable iff (!reset_n) (SUB == 0) |-> (result[3] == 0) |-> (OVFL == 0)
    );
    // Check that the result is within the valid range for 4-bit signed numbers
    check_result_range: assert property (
        @(posedge clk) disable iff (!reset_n) (result[3] == 1) |-> (result[2:0] == 3'b111)
    );
    check_result_range_add: assert property (
        @(posedge clk) disable iff (!reset_n) (result[3] == 0) |-> (result[2:0] == 3'b000)
    );
    // Check that the result is within the valid range for 4-bit unsigned numbers
    check_result_range_unsigned: assert property (
        @(posedge clk) disable iff (!reset_n) (result[3] == 0) |-> (result[2:0] == 3'b111)
    );
    check_result_range_unsigned_add: assert property (
        @(posedge clk) disable iff (!reset_n) (result[3] == 1) |-> (result[2:0] == 3'b000)
    );
endmodule
```