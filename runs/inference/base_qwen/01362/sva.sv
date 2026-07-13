module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    output logic [15:0] result
);
    // Combinational logic, so use @(posedge clk)
    // Addition operation
    addition_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b00) |-> (result == A + B)
    );
    // Subtraction operation
    subtraction_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b01) |-> (result == A - B)
    );
    // Multiplication operation
    multiplication_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b10) |-> (result == A * B)
    );
    // Division operation
    division_check: assert property (
        @(posedge clk) disable iff (!reset_n) (op == 2'b11) |-> (result == A / B)
    );
endmodule