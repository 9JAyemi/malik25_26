module padder1_sva (
    input logic        clk,
    input logic [31:0] in,
    input logic [1:0]  byte_num,
    input logic [31:0] out
);

    // byte_num 0 forces the output to 0x01000000.
    check_byte_num_zero_value: assert property (
        @(posedge clk)
        (byte_num === 2'd0) |-> (out === 32'h1000000)
    );

    // byte_num 1 keeps the top byte and appends 0x010000.
    check_byte_num_one_value: assert property (
        @(posedge clk)
        (byte_num === 2'd1) |-> (out === {in[31:24], 24'h010000})
    );

    // byte_num 2 keeps the top two bytes and appends 0x0100.
    check_byte_num_two_value: assert property (
        @(posedge clk)
        (byte_num === 2'd2) |-> (out === {in[31:16], 16'h0100})
    );

    // byte_num 3 keeps the top three bytes and appends 0x01.
    check_byte_num_three_value: assert property (
        @(posedge clk)
        (byte_num === 2'd3) |-> (out === {in[31:8], 8'h01})
    );

    // Stable inputs must produce a stable output.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk)
        ($stable(in) && $stable(byte_num)) |-> $stable(out)
    );

endmodule