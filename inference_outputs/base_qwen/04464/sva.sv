```systemverilog
module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);
    // The logic is purely combinational as there are no clocked signals.

    // Sum calculation is correct
    sum_correct: assert property (
        @(posedge CLK) disable iff (!RESETn) (A + B == S)
    );

    // Carry out calculation is correct
    carry_out_correct: assert property (
        @(posedge CLK) disable iff (!RESETn) (Cout == (A + B) > 4'b1111)
    );

endmodule
```