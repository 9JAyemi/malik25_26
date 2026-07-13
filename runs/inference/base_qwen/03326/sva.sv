module sky130_fd_sc_hdll__or4bb_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N,
    output logic X
);
    // NAND gate output
    wire nand0_out;
    // OR gate output
    wire or0_out_X;

    // NAND gate
    nand nand0 (nand0_out, D_N, C_N);
    // OR gate
    or   or0   (or0_out_X, B, A, nand0_out);
    // Buffer
    buf  buf0  (X, or0_out_X);

    // NAND gate output should be the negation of C_N and D_N
    nand_output_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (nand0_out == ~(C_N & D_N))
    );

    // OR gate output should be the OR of B, A, and NAND gate output
    or_output_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (or0_out_X == (B | A | nand0_out))
    );

    // Buffer output should be the same as OR gate output
    buffer_output_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == or0_out_X)
    );

    // NAND gate output should be a valid logic level (0 or 1)
    nand_output_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (nand0_out inside {0, 1})
    );

    // OR gate output should be a valid logic level (0 or 1)
    or_output_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (or0_out_X inside {0, 1})
    );

    // Buffer output should be a valid logic level (0 or 1)
    buffer_output_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (X inside {0, 1})
    );

    // NAND gate output should not change when A, B, C_N, and D_N are stable
    nand_output_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (nand0_out |-> (A | B | C_N | D_N))
    );

    // OR gate output should not change when A, B, C_N, and D_N are stable
    or_output_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (or0_out_X |-> (A | B | C_N | D_N))
    );

    // Buffer output should not change when A, B, C_N, and D_N are stable
    buffer_output_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (X |-> (A | B | C_N | D_N))
    );

    // NAND gate output should be 0 when C_N and D_N are both 0
    nand_output_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((C_N == 0) && (D_N == 0) |-> (nand0_out == 0))
    );

    // OR gate output should be 1 when A, B, or NAND gate output is 1
    or_output_one: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 1) || (B == 1) || (nand0_out == 1) |-> (or0_out_X == 1))
    );
endmodule