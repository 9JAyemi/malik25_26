module top_module_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] D,
    input logic [3:0] C
);

    // D is always one of the 0-to-3 encoded values.
    check_d_upper_bits_zero: assert property (
        @(posedge clk) D[3:2] == 2'b00
    );

    // C is always one of the 0-to-3 encoded values.
    check_c_upper_bits_zero: assert property (
        @(posedge clk) C[3:2] == 2'b00
    );

    // When in0 is greater, the outputs encode in0.
    check_encode_in0_when_greater: assert property (
        @(posedge clk)
        (in0 > in1) |-> (D == {2'b00, in0[3:2]} && C == {2'b00, in0[1:0]})
    );

    // When in0 is not greater, the outputs encode in1.
    check_encode_in1_when_not_greater: assert property (
        @(posedge clk)
        !(in0 > in1) |-> (D == {2'b00, in1[3:2]} && C == {2'b00, in1[1:0]})
    );

endmodule