module gray_code_converter_sva (
    input  logic clk,              // sampling clock for assertions
    input  logic [3:0] binary_in,
    input  logic select,
    input  logic [3:0] gray_out
);
    // LSB always matches binary_in[0].
    check_lsb_matches: assert property (
        @(posedge clk) (gray_out[0] == binary_in[0])
    );

    // When select=0, output passes through binary_in.
    check_passthrough_when_select0: assert property (
        @(posedge clk) (!select) |-> (gray_out == binary_in)
    );

    // When select=1, gray_out[1] is binary_in[0] XOR binary_in[1].
    check_gray_bit1_when_select1: assert property (
        @(posedge clk) (select) |-> (gray_out[1] == (binary_in[0] ^ binary_in[1]))
    );

    // When select=1, gray_out[2] is binary_in[1] XOR binary_in[2].
    check_gray_bit2_when_select1: assert property (
        @(posedge clk) (select) |-> (gray_out[2] == (binary_in[1] ^ binary_in[2]))
    );

    // When select=1, gray_out[3] is binary_in[2] XOR binary_in[3].
    check_gray_bit3_when_select1: assert property (
        @(posedge clk) (select) |-> (gray_out[3] == (binary_in[2] ^ binary_in[3]))
    );

    // When select=1, full vector matches Gray-code mapping.
    check_full_gray_mapping_when_select1: assert property (
        @(posedge clk) (select) |-> (gray_out == { (binary_in[2] ^ binary_in[3]),
                                                   (binary_in[1] ^ binary_in[2]),
                                                   (binary_in[0] ^ binary_in[1]),
                                                   (binary_in[0]) })
    );

    // If inputs are stable across cycles, output remains stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) ($stable(binary_in) && $stable(select)) |-> $stable(gray_out)
    );
endmodule