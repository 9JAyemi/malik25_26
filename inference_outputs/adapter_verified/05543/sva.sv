module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic CLK,   // sampling clock for assertions
    input logic A,
    input logic Y
);

// Y is always the logical inversion of A.
    check_inversion_function: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == ~A)
    );

// A low input drives Y high.
    check_low_input_drives_high_output: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 1'b0) |-> (Y == 1'b1)
    );

// A high input drives Y low.
    check_high_input_drives_low_output: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 1'b1) |-> (Y == 1'b0)
    );

// Y can only be high when A is low.
    check_output_high_implies_input_low: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b1) |-> (A == 1'b0)
    );

// Y can only be low when A is high.
    check_output_low_implies_input_high: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b0) |-> (A == 1'b1)
    );

endmodule
