module sky130_fd_sc_hd__lpflow_inputiso1p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);

    // X must implement the OR of A and SLEEP.
    check_or_gate_function: assert property (
        @($global_clock) X == (A | SLEEP)
    );

endmodule