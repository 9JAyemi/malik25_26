module assertions (
    input logic clk,
    input logic rst_n,
    input logic I,
    input logic A,
    input logic B,
    input logic S,
    output logic O,
    output logic Y
);
    // Inverter behavior: O should be the negation of I
    inverter_behavior: assert property (
        @(posedge clk) disable iff (!rst_n) O == ~I
    );

    // AND gate behavior: Y should be the AND of A and B
    and_gate_behavior: assert property (
        @(posedge clk) disable iff (!rst_n) Y == (A & B)
    );

    // MUX 2to1 behavior: Y should be A if S is 0, otherwise B
    mux_2to1_behavior: assert property (
        @(posedge clk) disable iff (!rst_n) Y == (S ? B : A)
    );
endmodule