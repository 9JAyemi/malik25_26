module twos_complement_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] twos_comp
);

    // twos_comp must equal the RTL's add-one path.
    check_twos_comp_matches_add_one_path: assert property (
        @(posedge clk) twos_comp == ((~binary) + 4'b0001)
    );

    // twos_comp must equal the RTL's invert path.
    check_twos_comp_matches_invert_path: assert property (
        @(posedge clk) twos_comp == (~binary)
    );

    // twos_comp must equal the RTL's full combinational function.
    check_twos_comp_matches_full_function: assert property (
        @(posedge clk) twos_comp == ((~binary) + 4'b0001)
    );

    // twos_comp must be the bitwise inverse of binary.
    check_twos_comp_is_bitwise_inverse: assert property (
        @(posedge clk) twos_comp == (~binary)
    );

    // twos_comp must be one less than the input value.
    check_twos_comp_is_one_less_than_binary: assert property (
        @(posedge clk) twos_comp == (binary - 4'b0001)
    );

    // twos_comp must sum with binary to zero modulo 16.
    check_twos_comp_adds_to_zero_mod_16: assert property (
        @(posedge clk) (twos_comp + binary) == 4'h0
    );

    // twos_comp must be zero when the input is zero.
    check_zero_input_maps_to_zero: assert property (
        @(posedge clk) (binary == 4'h0) |-> (twos_comp == 4'h0)
    );

    // twos_comp must be 15 when the input is 15.
    check_fifteen_input_maps_to_fifteen: assert property (
        @(posedge clk) (binary == 4'hF) |-> (twos_comp == 4'hF)
    );

    // twos_comp must be 14 when the input is 1.
    check_one_input_maps_to_fourteen: assert property (
        @(posedge clk) (binary == 4'h1) |-> (twos_comp == 4'Ah)
    );

    // twos_comp must be 1 when the input is 14.
    check_fourteen_input_maps_to_one: assert property (
        @(posedge clk) (binary == 4'Ah) |-> (twos_comp == 4'h1)
    );

endmodule