module section2_schematic_sva (
    input logic clk,
    input logic n63,
    input logic Z_B,
    input logic n62,
    input logic Len_int,
    input logic Ren_int
);

    // Len_int matches the implemented combinational equation.
    check_len_int_equation: assert property (
        @(posedge clk)
        Len_int == ((n63 & Z_B) | ((~n63 & ~n62) & (~Z_B & n62)))
    );

    // Ren_int matches the implemented combinational equation.
    check_ren_int_equation: assert property (
        @(posedge clk)
        Ren_int == ((~n63 & ~n62) & (~Z_B & n62))
    );

    // Len_int is high when both n63 and Z_B are high.
    check_len_int_high_when_both_high: assert property (
        @(posedge clk)
        (n63 & Z_B) |-> Len_int
    );

    // Len_int is high when both n63 and Z_B are low.
    check_len_int_high_when_both_low: assert property (
        @(posedge clk)
        (~n63 & ~Z_B) |-> Len_int
    );

    // Len_int is low when n63 is high and Z_B is low.
    check_len_int_low_when_n63_high_zb_low: assert property (
        @(posedge clk)
        (n63 & ~Z_B) |-> !Len_int
    );

    // Len_int is low when n63 is low and Z_B is high.
    check_len_int_low_when_n63_low_zb_high: assert property (
        @(posedge clk)
        (~n63 & Z_B) |-> !Len_int
    );

    // Ren_int is high only for the implemented low-low-high case.
    check_ren_int_high_only_for_low_low_high: assert property (
        @(posedge clk)
        Ren_int == ((~n63 & ~n62) & (~Z_B & n62))
    );

    // Ren_int is low when n63 is high.
    check_ren_int_low_when_n63_high: assert property (
        @(posedge clk)
        n63 |-> !Ren_int
    );

    // Ren_int is low when Z_B is high.
    check_ren_int_low_when_zb_high: assert property (
        @(posedge clk)
        Z_B |-> !Ren_int
    );

    // Ren_int is low when n62 is low.
    check_ren_int_low_when_n62_low: assert property (
        @(posedge clk)
        ~n62 |-> !Ren_int
    );

    // Ren_int is high when n63 and Z_B are low and n62 is high.
    check_ren_int_high_when_low_low_high: assert property (
        @(posedge clk)
        (~n63 & ~Z_B & n62) |-> Ren_int
    );

endmodule