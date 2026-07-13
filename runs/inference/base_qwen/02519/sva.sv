module addsub_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic C,
    output logic [15:0] Q
);
    // Combinational logic: Q is the result of either A + B or A - B based on the value of C
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (Q == (C == 1'b1) ? A - B : A + B)
    );
endmodule