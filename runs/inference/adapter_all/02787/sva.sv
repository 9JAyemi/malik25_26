module twos_complement_sva (
    input logic [3:0] binary,
    input logic [3:0] twos_comp
);
    // twos_comp equals bitwise NOT of binary plus 1.
    check_twos_comp_def: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp + binary equals 4'b0000 (mod 16).
    check_additive_inverse: assert property (
        @(posedge binary[0]) (twos_comp + binary) == 4'b0000
    );

    // twos_comp equals binary - 1 (mod 16).
    check_minus_one_equiv: assert property (
        @(posedge binary[0]) twos_comp == (binary - 4'b0001)
    );

    // twos_comp equals ~binary + 1 (bitwise form).
    check_bitwise_form: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form_2: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form_3: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form_4: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form_5: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );

    // twos_comp equals ~binary + 1 (arithmetic form).
    check_arithmetic_form_6: assert property (
        @(posedge binary[0]) twos_comp == (~binary + 4'b0001)
    );
endmodule