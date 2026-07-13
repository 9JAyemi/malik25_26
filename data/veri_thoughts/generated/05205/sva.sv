module system_vga_hessian_0_0_bindec_0_assertions (
    input logic clk,
    input logic [2:0] enb_array,
    input logic enb,
    input logic [1:0] addrb
);

    // Checks enb_array[0] matches its combinational equation.
    check_enb_array_bit0_function: assert property (
        @(posedge clk) enb_array[0] == ((addrb[1] & ~addrb[0]) | enb)
    );

    // Checks enb_array[1] matches its combinational equation.
    check_enb_array_bit1_function: assert property (
        @(posedge clk) enb_array[1] == ((addrb[0] & ~addrb[1]) | enb)
    );

    // Checks enb_array[2] matches its combinational equation.
    check_enb_array_bit2_function: assert property (
        @(posedge clk) enb_array[2] == ((enb & ~addrb[0]) | addrb[1])
    );

    // Checks enb forces enb_array[1:0] high.
    check_enable_sets_low_bits: assert property (
        @(posedge clk) enb |-> (enb_array[1:0] == 2'b11)
    );

    // Checks addrb[1] directly forces enb_array[2] high.
    check_addrb1_sets_bit2: assert property (
        @(posedge clk) addrb[1] |-> enb_array[2]
    );

    // Checks bits 0 and 1 are never both high when enb is low.
    check_disabled_low_bits_mutually_exclusive: assert property (
        @(posedge clk) (!enb) |-> !(enb_array[0] && enb_array[1])
    );

    // Checks the disabled decode for addrb == 2'b00.
    check_disabled_decode_00: assert property (
        @(posedge clk) ((!enb) && (addrb == 2'b00)) |-> (enb_array == 3'b000)
    );

    // Checks the disabled decode for addrb == 2'b01.
    check_disabled_decode_01: assert property (
        @(posedge clk) ((!enb) && (addrb == 2'b01)) |-> (enb_array == 3'b010)
    );

    // Checks the disabled decode for addrb == 2'b10.
    check_disabled_decode_10: assert property (
        @(posedge clk) ((!enb) && (addrb == 2'b10)) |-> (enb_array == 3'b101)
    );

    // Checks the disabled decode for addrb == 2'b11.
    check_disabled_decode_11: assert property (
        @(posedge clk) ((!enb) && (addrb == 2'b11)) |-> (enb_array == 3'b100)
    );

endmodule