module binary_to_gray_sva (
    input logic [3:0] binary_in,
    input logic       clk,
    input logic [3:0] gray_out
);

// gray_out[3] captures the previous cycle's binary_in[3].
    check_gray_msb_capture: assert property (
        @(posedge clk) 1'b1 |=> (gray_out[3] == $past(binary_in[3]))
    );

// gray_out[2] is the previous cycle's binary_in[3] XOR binary_in[2].
    check_gray_bit2_xor: assert property (
        @(posedge clk) 1'b1 |=> (gray_out[2] == ($past(binary_in[3]) ^ $past(binary_in[2])))
    );

// gray_out[1] is the previous cycle's binary_in[2] XOR binary_in[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) 1'b1 |=> (gray_out[1] == ($past(binary_in[2]) ^ $past(binary_in[1])))
    );

// gray_out[0] is the previous cycle's binary_in[1] XOR binary_in[0].
    check_gray_bit0_xor: assert property (
        @(posedge clk) 1'b1 |=> (gray_out[0] == ($past(binary_in[1]) ^ $past(binary_in[0])))
    );

endmodule
