
module xor_shift_register (
    input a, // Input for AND gate
    input b, // Input for AND gate
    input [7:0] d, // Input for shift register
    input clk, // Clock input for shift register
    output [7:0] q // 8-bit output after XOR operation
);

    // 2-input AND gate using only NOR gates
    wire n1, n2, n3, n4, n5, n6, n7, n8;
    assign n1 = ~(a | b);
    assign n2 = ~(n1 | n1);
    assign n3 = ~(n2 | n2);
    assign n4 = ~(n3 | n3);
    assign n5 = ~(n4 | n4);
    assign n6 = ~(n5 | n5);
    assign n7 = ~(n6 | n6);
    assign n8 = ~(n7 | n7);
    wire and_out = ~(n8 | n8);

    // 8-bit shift register
    reg [7:0] shift_reg;
    always @(posedge clk) begin
        shift_reg <= {shift_reg[6:0], 1'b0};
    end

    // Bitwise XOR operation
    assign q = shift_reg ^ and_out;

endmodule
