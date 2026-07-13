module seven_segment_decoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic common_anode,
    input logic [6:0] out
);

    // Local function mirroring the decoder's base (common-cathode) mapping
    function automatic logic [6:0] base_decode (input logic [3:0] x);
        case (x)
            4'b0000: base_decode = 7'b1111110; // 0
            4'b0001: base_decode = 7'b0110000; // 1
            4'b0010: base_decode = 7'b1101101; // 2
            4'b0011: base_decode = 7'b1111001; // 3
            4'b0100: base_decode = 7'b0110011; // 4
            4'b0101: base_decode = 7'b1011011; // 5
            4'b0110: base_decode = 7'b1011111; // 6
            4'b0111: base_decode = 7'b1110000; // 7
            4'b1000: base_decode = 7'b1111111; // 8
            4'b1001: base_decode = 7'b1111011; // 9
            4'b1010: base_decode = 7'b1110111; // A
            4'b1011: base_decode = 7'b0011111; // B
            4'b1100: base_decode = 7'b1001110; // C
            4'b1101: base_decode = 7'b0111101; // D
            4'b1110: base_decode = 7'b1001111; // E
            4'b1111: base_decode = 7'b1000111; // F
            default: base_decode = 7'b0000000; // Blank
        endcase
    endfunction

    ///// Functional mapping rules /////
    // When common_anode is LOW, out must equal the base decode of in.
    check_mapping_common_cathode: assert property (
        @(posedge clk) !common_anode |-> (out == base_decode(in))
    );

    // When common_anode is HIGH, out must be the bitwise inversion of the base decode.
    check_mapping_common_anode: assert property (
        @(posedge clk) common_anode |-> (out == ~base_decode(in))
    );

    // Out must invert when only common_anode toggles and in is stable.
    check_invert_on_ca_toggle: assert property (
        @(posedge clk) ($rose(common_anode) || $fell(common_anode)) && $stable(in) |-> (out == ~$past(out))
    );

    // For each hex digit, mapping must match the table when common_anode is LOW.
    check_0_cc: assert property (@(posedge clk) (!common_anode && in==4'h0) |-> out==7'b1111110);
    check_1_cc: assert property (@(posedge clk) (!common_anode && in==4'h1) |-> out==7'b0110000);
    check_2_cc: assert property (@(posedge clk) (!common_anode && in==4'h2) |-> out==7'b1101101);
    check_3_cc: assert property (@(posedge clk) (!common_anode && in==4'h3) |-> out==7'b1111001);
    check_4_cc: assert property (@(posedge clk) (!common_anode && in==4'h4) |-> out==7'b0110011);
    check_5_cc: assert property (@(posedge clk) (!common_anode && in==4'h5) |-> out==7'b1011011);
    check_6_cc: assert property (@(posedge clk) (!common_anode && in==4'h6) |-> out==7'b1011111);
    check_7_cc: assert property (@(posedge clk) (!common_anode && in==4'h7) |-> out==7'b1110000);
    check_8_cc: assert property (@(posedge clk) (!common_anode && in==4'h8) |-> out==7'b1111111);
    check_9_cc: assert property (@(posedge clk) (!common_anode && in==4'h9) |-> out==7'b1111011);
    check_A_cc: assert property (@(posedge clk) (!common_anode && in==4'hA) |-> out==7'b1110111);
    check_B_cc: assert property (@(posedge clk) (!common_anode && in==4'hB) |-> out==7'b0011111);
    check_C_cc: assert property (@(posedge clk) (!common_anode && in==4'hC) |-> out==7'b1001110);
    check_D_cc: assert property (@(posedge clk) (!common_anode && in==4'hD) |-> out==7'b0111101);
    check_E_cc: assert property (@(posedge clk) (!common_anode && in==4'hE) |-> out==7'b1001111);
    check_F_cc: assert property (@(posedge clk) (!common_anode && in==4'hF) |-> out==7'b1000111);

    // For each hex digit, mapping must match the inverted table when common_anode is HIGH.
    check_0_ca: assert property (@(posedge clk) ( common_anode && in==4'h0) |-> out==~7'b1111110);
    check_1_ca: assert property (@(posedge clk) ( common_anode && in==4'h1) |-> out==~7'b0110000);
    check_2_ca: assert property (@(posedge clk) ( common_anode && in==4'h2) |-> out==~7'b1101101);
    check_3_ca: assert property (@(posedge clk) ( common_anode && in==4'h3) |-> out==~7'b1111001);
    check_4_ca: assert property (@(posedge clk) ( common_anode && in==4'h4) |-> out==~7'b0110011);
    check_5_ca: assert property (@(posedge clk) ( common_anode && in==4'h5) |-> out==~7'b1011011);
    check_6_ca: assert property (@(posedge clk) ( common_anode && in==4'h6) |-> out==~7'b1011111);
    check_7_ca: assert property (@(posedge clk) ( common_anode && in==4'h7) |-> out==~7'b1110000);
    check_8_ca: assert property (@(posedge clk) ( common_anode && in==4'h8) |-> out==~7'b1111111);
    check_9_ca: assert property (@(posedge clk) ( common_anode && in==4'h9) |-> out==~7'b1111011);
    check_A_ca: assert property (@(posedge clk) ( common_anode && in==4'hA) |-> out==~7'b1110111);
    check_B_ca: assert property (@(posedge clk) ( common_anode && in==4'hB) |-> out==~7'b0011111);
    check_C_ca: assert property (@(posedge clk) ( common_anode && in==4'hC) |-> out==~7'b1001110);
    check_D_ca: assert property (@(posedge clk) ( common_anode && in==4'hD) |-> out==~7'b0111101);
    check_E_ca: assert property (@(posedge clk) ( common_anode && in==4'hE) |-> out==~7'b1001111);
    check_F_ca: assert property (@(posedge clk) ( common_anode && in==4'hF) |-> out==~7'b1000111);

endmodule