module sky130_fd_sc_hdll__clkinvlp_assertions (
    input logic Y,
    input logic A
);

    // Y must always be the logical inverse of A.
    check_inverter_truth_table: assert property (
        @($global_clock) (Y === ~A)
    );

endmodule