module and2b (
    output X,
    input A_N,
    input B
);

    // Module ports
    //output X;
    //input A_N;
    //input B;

    // Local signals
    wire not0_out;
    wire and0_out_X;
    wire pwrgood_pp0_out_X;

    //Name Output Other arguments
    not not0 (not0_out, A_N);
    and and0 (and0_out_X, not0_out, B);
    //sky130_fd_sc_hd__udp_pwrgood_pp$PG pwrgood_pp0 (pwrgood_pp0_out_X, and0_out_X, 1'b1, 1'b0);
    buf buf0 (X, and0_out_X);

endmodule