```systemverilog
module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic X
);
    // Combinational logic, so use @(posedge clk)
    // X is the result of ANDing A, B, C, and D
    combinational_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A & B & C & D))
    );
endmodule
```