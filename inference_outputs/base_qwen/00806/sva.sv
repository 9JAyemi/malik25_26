module sky130_fd_sc_ls__or4b_sva (
    input logic CLK,
    input logic D_N,
    input logic A,
    input logic B,
    input logic C,
    output logic X
);
    // The OR4B module has combinational logic, so we will use @(posedge CLK) for assertions.

    // The output X is the result of the OR operation on A, B, C, and the inverted D_N.
    // The OR operation is performed on the inputs A, B, C, and the inverted D_N.
    // The output X is the result of the OR operation.
    or4b_output: assert property (
        @(posedge CLK) disable iff (!CLK) (X == (A | B | C | ~D_N))
    );
endmodule