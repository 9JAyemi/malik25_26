module sky130_fd_sc_ms__xnor3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must implement the 3-input XNOR function.
    check_xnor_function: assert property (
        @(posedge clk) X == ~(A ^ B ^ C)
    );

    // All-zero inputs must drive X high.
    check_all_zero_drives_high: assert property (
        @(posedge clk) (!A && !B && !C) |-> X
    );

    // Exactly one high input must drive X low.
    check_single_one_drives_low: assert property (
        @(posedge clk)
        (( A && !B && !C) ||
         (!A &&  B && !C) ||
         (!A && !B &&  C)) |-> !X
    );

    // Exactly two high inputs must drive X high.
    check_double_one_drives_high: assert property (
        @(posedge clk)
        (( A &&  B && !C) ||
         ( A && !B &&  C) ||
         (!A &&  B &&  C)) |-> X
    );

    // All-one inputs must drive X low.
    check_all_one_drives_low: assert property (
        @(posedge clk) (A && B && C) |-> !X
    );

endmodule