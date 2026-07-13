module mux4_sva (
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    output logic X
);
    // Combinational logic, use @(posedge clk)
    // X should be the result of the multiplexer logic
    mux_output: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A0 & ~S0 & ~S1) | (A1 & S0 & ~S1) | (A2 & ~S0 & S1) | (A3 & S0 & S1))
    );
endmodule