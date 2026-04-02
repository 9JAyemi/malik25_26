module sky130_fd_sc_ms__o41a_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    output logic X
);
    // The logic is purely combinational as there are no sequential elements.

    // The OR gate outputs 1 if any of A1, A2, A3, or A4 is 1.
    // The AND gate outputs 1 if the OR gate output is 1 and B1 is 1.
    // The buffer drives the output X with the AND gate output.

    // The OR gate output is always determined by the current values of A1, A2, A3, and A4.
    // The AND gate output is always determined by the current values of the OR gate output and B1.
    // The buffer output is always determined by the current value of the AND gate output.

    // Since the logic is purely combinational, we use @(posedge CLK) to clock the assertions.

    // The OR gate output is always determined by the current values of A1, A2, A3, and A4.
    or_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (or0_out == (A1 | A2 | A3 | A4))
    );

    // The AND gate output is always determined by the current values of the OR gate output and B1.
    and_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (and0_out_X == (or0_out & B1))
    );

    // The buffer output is always determined by the current value of the AND gate output.
    buffer_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == and0_out_X)
    );

endmodule