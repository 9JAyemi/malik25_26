module final_module_sva (
    input logic clk,
    input logic [15:0] in,
    output logic [15:0] out
);
    wire [7:0] out1;
    wire [7:0] out2;

    barrel_shifter bs(
        .in(in),
        .out1(out1),
        .out2(out2)
    );

    d_flip_flop ff(
        .clk(clk),
        .d(out1[7] & out2[0]),
        .q(out[0])
    );

    always @(*) begin
        out = {out1, out2, out[0]};
    end

    ///// Barrel shifter outputs /////
    // out1 should always be the lower 8 bits of the input
    check_out1: assert property (
        @(posedge clk) disable iff (!clk) out1 == in[7:0]
    );

    // out2 should always be the upper 8 bits of the input
    check_out2: assert property (
        @(posedge clk) disable iff (!clk) out2 == in[15:8]
    );

    ///// D flip-flop behavior /////
    // The output of the D flip-flop should be the AND of the 8th bit of out1 and the 0th bit of out2
    check_ff_output: assert property (
        @(posedge clk) disable iff (!clk) out[0] == (out1[7] & out2[0])
    );

    ///// Final output behavior /////
    // The final output should be the concatenation of out1, out2, and the output of the D flip-flop
    check_final_output: assert property (
        @(posedge clk) disable iff (!clk) out == {out1, out2, out[0]}
    );
endmodule