module section2_schematic_sva (
    input logic clk,
    input logic n63,
    input logic Z_B,
    input logic n62,
    input logic Len_int,
    input logic Ren_int
);

    // Len_int matches the implemented OR-of-products equation.
    check_len_equation: assert property (
        @(posedge clk)
        Len_int == ((n63 & Z_B) | ((~n63) & (~Z_B) & (~n62)))
    );

    // Ren_int matches the implemented OR-of-products equation.
    check_ren_equation: assert property (
        @(posedge clk)
        Ren_int == ((Z_B & n62) | ((~n63) & (~Z_B) & (~n62)))
    );

    // When Z_B is high, the outputs follow n63 and n62 directly.
    check_outputs_follow_inputs_when_zb_high: assert property (
        @(posedge clk)
        Z_B |-> ((Len_int == n63) && (Ren_int == n62))
    );

    // When Z_B is low, both outputs reduce to !n63 & !n62.
    check_outputs_when_zb_low: assert property (
        @(posedge clk)
        (!Z_B) |-> ((Len_int == ((!n63) && (!n62))) && (Ren_int == ((!n63) && (!n62))))
    );

    // With Z_B low, any high input forces both outputs low.
    check_outputs_low_when_zb_low_and_any_input_high: assert property (
        @(posedge clk)
        ((!Z_B) && (n63 || n62)) |-> ((!Len_int) && (!Ren_int))
    );

    // With all three inputs low, both outputs must be high.
    check_outputs_high_when_all_inputs_low: assert property (
        @(posedge clk)
        ((!Z_B) && (!n63) && (!n62)) |-> (Len_int && Ren_int)
    );

endmodule