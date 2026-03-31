module reverse_last_two_bits_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // out is the previous cycle's concatenation of in[1:0] and in[3:2].
    check_out_matches_previous_input: assert property (
        @(posedge clk) 1'b1 |=> (out == { $past(in[1:0]), $past(in[3:2]) })
    );

    // out[0] is the previous cycle's in[1].
    check_out0_matches_previous_in1: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == $past(in[1]))
    );

    // out[1] is the previous cycle's in[3].
    check_out1_matches_previous_in3: assert property (
        @(posedge clk) 1'b1 |=> (out[1] == $past(in[3]))
    );

endmodule