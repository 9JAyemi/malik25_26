module binary_to_gray_assertions (
    input logic       clk,
    input logic [3:0] binary,
    input logic [3:0] gray
);

    function automatic logic [3:0] bin2gray(input logic [3:0] b);
        case (b)
            4'b0000: bin2gray = 4'b0000;
            4'b0001: bin2gray = 4'b0001;
            4'b0010: bin2gray = 4'b0011;
            4'b0011: bin2gray = 4'b0010;
            4'b0100: bin2gray = 4'b0110;
            4'b0101: bin2gray = 4'b0111;
            4'b0110: bin2gray = 4'b0101;
            4'b0111: bin2gray = 4'b0100;
            4'b1000: bin2gray = 4'b1100;
            4'b1001: bin2gray = 4'b1101;
            4'b1010: bin2gray = 4'b1111;
            4'b1011: bin2gray = 4'b1110;
            4'b1100: bin2gray = 4'b1010;
            4'b1101: bin2gray = 4'b1011;
            4'b1110: bin2gray = 4'b1001;
            4'b1111: bin2gray = 4'b1000;
            default: bin2gray = 4'bxxxx;
        endcase
    endfunction

    // Gray matches the registered table lookup of the prior binary input.
    check_gray_matches_lookup: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> (gray == bin2gray($past(binary)))
    );

    // Gray[3] is the registered MSB of the prior binary input.
    check_gray_bit3_relation: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> (gray[3] == $past(binary[3]))
    );

    // Gray[2] is the registered XOR of prior binary[3] and binary[2].
    check_gray_bit2_relation: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> (gray[2] == ($past(binary[3]) ^ $past(binary[2])))
    );

    // Gray[1] is the registered XOR of prior binary[2] and binary[1].
    check_gray_bit1_relation: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> (gray[1] == ($past(binary[2]) ^ $past(binary[1])))
    );

    // Gray[0] is the registered XOR of prior binary[1] and binary[0].
    check_gray_bit0_relation: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> (gray[0] == ($past(binary[1]) ^ $past(binary[0])))
    );

    // A stable binary input across cycles keeps gray stable one cycle later.
    check_stable_input_stable_output: assert property (
        @(posedge clk)
        (!$isunknown($past(binary)) && !$isunknown($past(binary,2)) && ($past(binary) == $past(binary,2)))
        |-> (gray == $past(gray))
    );

    // A changed binary input across cycles changes gray one cycle later.
    check_changed_input_changed_output: assert property (
        @(posedge clk)
        (!$isunknown($past(binary)) && !$isunknown($past(binary,2)) && ($past(binary) != $past(binary,2)))
        |-> (gray != $past(gray))
    );

    // A known prior binary input produces a known gray output.
    check_known_input_known_output: assert property (
        @(posedge clk) !$isunknown($past(binary)) |-> !$isunknown(gray)
    );

endmodule