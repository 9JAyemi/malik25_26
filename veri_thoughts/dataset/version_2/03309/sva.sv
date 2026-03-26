module INV3_sva (
    input logic clk,
    input logic [2:0] in,
    input logic out
);

    // out matches the inverted-input AND function in the RTL.
    check_out_matches_inverted_and: assert property (
        @(posedge clk) out == ((~in[0]) & (~in[1]) & (~in[2]))
    );

    // An all-zero input vector drives out high.
    check_all_zero_input_drives_high: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 1'b1)
    );

    // A high in[0] forces out low.
    check_in0_high_forces_out_low: assert property (
        @(posedge clk) in[0] |-> (out == 1'b0)
    );

    // A high in[1] forces out low.
    check_in1_high_forces_out_low: assert property (
        @(posedge clk) in[1] |-> (out == 1'b0)
    );

    // A high in[2] forces out low.
    check_in2_high_forces_out_low: assert property (
        @(posedge clk) in[2] |-> (out == 1'b0)
    );

endmodule