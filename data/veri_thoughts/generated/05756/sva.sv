module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic [1:0]  select,
    input logic [7:0]  product,
    input logic [3:0]  booth_input,
    input logic [7:0]  booth_output,
    input logic [7:0]  register_a,
    input logic [7:0]  register_b,
    input logic [7:0]  register_p
);

    // Decoder maps select 00 to 0001.
    check_decoder_select_00: assert property (
        @(posedge clk) disable iff (reset)
        (select == 2'b00) |-> (booth_input == 4'b0001)
    );

    // Decoder maps select 01 to 0010.
    check_decoder_select_01: assert property (
        @(posedge clk) disable iff (reset)
        (select == 2'b01) |-> (booth_input == 4'b0010)
    );

    // Decoder maps select 10 to 0100.
    check_decoder_select_10: assert property (
        @(posedge clk) disable iff (reset)
        (select == 2'b10) |-> (booth_input == 4'b0100)
    );

    // Decoder maps select 11 to 1000.
    check_decoder_select_11: assert property (
        @(posedge clk) disable iff (reset)
        (select == 2'b11) |-> (booth_input == 4'b1000)
    );

    // Multiplier output always reflects register_p.
    check_booth_output_matches_register_p: assert property (
        @(posedge clk) disable iff (reset)
        (booth_output == register_p)
    );

    // Top-level product is cleared by a reset cycle.
    check_top_reset_clears_product: assert property (
        @(posedge clk)
        reset |=> (product == 8'b0)
    );

    // Multiplier state is cleared by a reset cycle.
    check_booth_reset_clears_state: assert property (
        @(posedge clk)
        reset |=> (register_a == 8'b0 && register_b == 8'b0 && register_p == 8'b0 && booth_output == 8'b0)
    );

    // Top-level product registers the prior booth_output value.
    check_top_product_captures_booth_output: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (product == $past(booth_output))
    );

    // register_b captures b with zero extension.
    check_register_b_captures_b: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (register_b == {4'b0000, $past(b)})
    );

    // register_a follows the final right-shift assignment.
    check_register_a_shifts_previous_value: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (register_a == ($past(register_a) >> 1))
    );

    // booth_input[1:0] == 00 causes register_p to add register_b.
    check_register_p_add_on_00: assert property (
        @(posedge clk) disable iff (reset)
        (booth_input[1:0] == 2'b00) |=> (register_p == ($past(register_p) + $past(register_b)))
    );

    // booth_input[1:0] == 01 causes register_p to subtract register_b.
    check_register_p_sub_on_01: assert property (
        @(posedge clk) disable iff (reset)
        (booth_input[1:0] == 2'b01) |=> (register_p == ($past(register_p) - $past(register_b)))
    );

    // booth_input[1:0] == 10 causes register_p to add register_b.
    check_register_p_add_on_10: assert property (
        @(posedge clk) disable iff (reset)
        (booth_input[1:0] == 2'b10) |=> (register_p == ($past(register_p) + $past(register_b)))
    );

endmodule