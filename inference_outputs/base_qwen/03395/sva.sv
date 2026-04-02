module AND3_assertions (
    input logic A,
    input logic B,
    input logic C,
    output logic Z
);
    // Combinational logic, so use @(posedge clk)
    // Z should always be the result of A & B & C
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) Z == (A & B & C)
    );
endmodule