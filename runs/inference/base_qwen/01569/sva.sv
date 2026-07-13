module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] S,
    output logic Cout
);
    // Combinational logic, so use @(posedge clk)
    // Sum calculation must be correct
    sum_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (Sum == {1'b0, A} + {1'b0, B} + Cin)
    );
    // S should be the lower 4 bits of Sum
    s_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (S == Sum[3:0])
    );
    // Cout should be the 5th bit of Sum
    cout_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (Cout == Sum[4])
    );
endmodule