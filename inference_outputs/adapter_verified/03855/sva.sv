module sky130_fd_sc_ls__clkinv_sva (
    input logic clk,
    input logic A,
    input logic Y
);

// Y must be the bitwise inversion of A.
    check_inversion: assert property (
        @(posedge clk) Y == ~A
    );

// A high input must drive Y low.
    check_a_high_drives_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

// A low input must drive Y high.
    check_a_low_drives_y_high: assert property (
        @(posedge clk) !A |-> Y
    );

endmodule
