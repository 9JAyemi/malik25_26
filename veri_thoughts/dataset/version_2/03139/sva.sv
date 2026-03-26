module display_sva (
    input logic        clk,
    input logic [15:0] disp_num,
    input logic [6:0]  seg,
    input logic [3:0]  anode
);

    function automatic logic [6:0] hex_to_seg(input logic [3:0] value);
        case (value)
            4'h0: hex_to_seg = 7'b1000000;
            4'h1: hex_to_seg = 7'b1111001;
            4'h2: hex_to_seg = 7'b0100100;
            4'h3: hex_to_seg = 7'b0110000;
            4'h4: hex_to_seg = 7'b0011001;
            4'h5: hex_to_seg = 7'b0010010;
            4'h6: hex_to_seg = 7'b0000010;
            4'h7: hex_to_seg = 7'b1111000;
            4'h8: hex_to_seg = 7'b0000000;
            4'h9: hex_to_seg = 7'b0010000;
            4'hA: hex_to_seg = 7'b0001000;
            4'hB: hex_to_seg = 7'b0000011;
            4'hC: hex_to_seg = 7'b1000110;
            4'hD: hex_to_seg = 7'b0100001;
            4'hE: hex_to_seg = 7'b0000110;
            4'hF: hex_to_seg = 7'b0001110;
            default: hex_to_seg = 7'bxxxxxxx;
        endcase
    endfunction

    // Anode must always select exactly one active-low digit.
    check_anode_valid_pattern: assert property (
        @(posedge clk)
        (anode == 4'b1110) || (anode == 4'b1101) || (anode == 4'b1011) || (anode == 4'b0111)
    );

    // Anode changes must follow the implemented round-robin order.
    check_anode_round_robin: assert property (
        @(posedge clk)
        $changed(anode) |-> (
            ($past(anode) == 4'b1110 && anode == 4'b1101) ||
            ($past(anode) == 4'b1101 && anode == 4'b1011) ||
            ($past(anode) == 4'b1011 && anode == 4'b0111) ||
            ($past(anode) == 4'b0111 && anode == 4'b1110)
        )
    );

    // When digit 0 is active, seg must encode disp_num[3:0].
    check_seg_matches_digit0: assert property (
        @(posedge clk)
        (anode == 4'b1110) |-> (seg == hex_to_seg(disp_num[3:0]))
    );

    // When digit 1 is active, seg must encode disp_num[7:4].
    check_seg_matches_digit1: assert property (
        @(posedge clk)
        (anode == 4'b1101) |-> (seg == hex_to_seg(disp_num[7:4]))
    );

    // When digit 2 is active, seg must encode disp_num[11:8].
    check_seg_matches_digit2: assert property (
        @(posedge clk)
        (anode == 4'b1011) |-> (seg == hex_to_seg(disp_num[11:8]))
    );

    // When digit 3 is active, seg must encode disp_num[15:12].
    check_seg_matches_digit3: assert property (
        @(posedge clk)
        (anode == 4'b0111) |-> (seg == hex_to_seg(disp_num[15:12]))
    );

    // With digit 0 held and its nibble unchanged, seg must stay unchanged.
    check_seg_stable_digit0: assert property (
        @(posedge clk)
        (anode == 4'b1110 && $stable(anode) && $stable(disp_num[3:0])) |-> $stable(seg)
    );

    // With digit 1 held and its nibble unchanged, seg must stay unchanged.
    check_seg_stable_digit1: assert property (
        @(posedge clk)
        (anode == 4'b1101 && $stable(anode) && $stable(disp_num[7:4])) |-> $stable(seg)
    );

    // With digit 2 held and its nibble unchanged, seg must stay unchanged.
    check_seg_stable_digit2: assert property (
        @(posedge clk)
        (anode == 4'b1011 && $stable(anode) && $stable(disp_num[11:8])) |-> $stable(seg)
    );

    // With digit 3 held and its nibble unchanged, seg must stay unchanged.
    check_seg_stable_digit3: assert property (
        @(posedge clk)
        (anode == 4'b0111 && $stable(anode) && $stable(disp_num[15:12])) |-> $stable(seg)
    );

endmodule