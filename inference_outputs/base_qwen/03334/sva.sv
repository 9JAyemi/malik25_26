```systemverilog
module four_bit_adder_sva (
    input logic Clock,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] Sum,
    output logic Cout
);
    // Sum should be the result of A + B + Cin
    sum_correct: assert property (
        @(posedge Clock) disable iff (!Clock) (Sum == A + B + Cin)
    );
    // Cout should be the carry out of the addition
    carry_out_correct: assert property (
        @(posedge Clock) disable iff (!Clock) (Cout == (A + B + Cin) >> 4)
    );
endmodule
```