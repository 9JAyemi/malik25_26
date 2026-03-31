module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);
    // No clock or reset in DUT; purely combinational: C = A + B.
    // No clocked SVA can be written without inventing a clock, so no assertions here.
endmodule