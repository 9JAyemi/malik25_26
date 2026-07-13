module sky130_fd_sc_ms__clkdlyinv5sd2_sva (
    input logic Y,
    input logic A
);
    // Y must be the inverse of A when A rises.
    check_inversion_at_A_rise: assert property (
        @(posedge A) (Y === ~A)
    );

    // Y must be the inverse of A when A falls.
    check_inversion_at_A_fall: assert property (
        @(negedge A) (Y === ~A)
    );

    // A must be the inverse of Y when Y rises.
    check_input_inverse_at_Y_rise: assert property (
        @(posedge Y) (A === ~Y)
    );

    // A must be the inverse of Y when Y falls.
    check_input_inverse_at_Y_fall: assert property (
        @(negedge Y) (A === ~Y)
    );
endmodule