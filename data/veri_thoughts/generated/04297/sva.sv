module encoder_sva (
    input logic [7:0] in,
    input logic       clk,
    input logic [2:0] out
);

    // out[0] goes high two clocks after any contributing input bit is high.
    check_out0_high_encoding: assert property (
        @(posedge clk)
        ((in[0] | in[1] | in[3] | in[4] | in[6]) == 1'b1) |-> ##2 (out[0] == 1'b1)
    );

    // out[0] stays low two clocks after all contributing input bits are low.
    check_out0_low_encoding: assert property (
        @(posedge clk)
        ((in[0] | in[1] | in[3] | in[4] | in[6]) == 1'b0) |-> ##2 (out[0] == 1'b0)
    );

    // out[1] goes high two clocks after any contributing input bit is high.
    check_out1_high_encoding: assert property (
        @(posedge clk)
        ((in[2] | in[3] | in[5] | in[6] | in[7]) == 1'b1) |-> ##2 (out[1] == 1'b1)
    );

    // out[1] stays low two clocks after all contributing input bits are low.
    check_out1_low_encoding: assert property (
        @(posedge clk)
        ((in[2] | in[3] | in[5] | in[6] | in[7]) == 1'b0) |-> ##2 (out[1] == 1'b0)
    );

    // out[2] goes high two clocks after any contributing input bit is high.
    check_out2_high_encoding: assert property (
        @(posedge clk)
        ((in[4] | in[5] | in[6] | in[7]) == 1'b1) |-> ##2 (out[2] == 1'b1)
    );

    // out[2] stays low two clocks after all contributing input bits are low.
    check_out2_low_encoding: assert property (
        @(posedge clk)
        ((in[4] | in[5] | in[6] | in[7]) == 1'b0) |-> ##2 (out[2] == 1'b0)
    );

endmodule