module section2_schematic_sva (
    input logic clk,
    input logic n63,
    input logic Z_B,
    input logic n62,
    input logic Len_int,
    input logic Ren_int
);

// Len_int equals n63 & Z_B.
    check_len_equals_and: assert property (
        @(posedge clk) Len_int == (n63 & Z_B)
    );

// Ren_int equals (n63 & Z_B) | (Z_B & n62).
    check_ren_equals_or: assert property (
        @(posedge clk) Ren_int == ((n63 & Z_B) | (Z_B & n62))
    );

// If Z_B is 0, both outputs must be 0.
    check_zero_when_zb_zero: assert property (
        @(posedge clk) (Z_B == 1'b0) |-> (Len_int == 1'b0 && Ren_int == 1'b0)
    );

// If Z_B is 1, Len_int equals n63 and Ren_int equals n62.
    check_outputs_when_zb_one: assert property (
        @(posedge clk) (Z_B == 1'b1) |-> (Len_int == n63 && Ren_int == n62)
    );

// If n63 is 0, both outputs must be 0.
    check_zero_when_n63_zero: assert property (
        @(posedge clk) (n63 == 1'b0) |-> (Len_int == 1'b0 && Ren_int == 1'b0)
    );

// If n62 is 0, Ren_int must be 0.
    check_ren_zero_when_n62_zero: assert property (
        @(posedge clk) (n62 == 1'b0) |-> (Ren_int == 1'b0)
    );

// If n63 is 1 and n62 is 1, both outputs must be 1.
    check_one_when_both_high: assert property (
        @(posedge clk) (n63 == 1'b1 && n62 == 1'b1) |-> (Len_int == 1'b1 && Ren_int == 1'b1)
    );

// If n63 is 1 and n62 is 0, Len_int must be 1 and Ren_int must be 0.
    check_len_one_ren_zero_when_n63_one_n62_zero: assert property (
        @(posedge clk) (n63 == 1'b1 && n62 == 1'b0) |-> (Len_int == 1'b1 && Ren_int == 1'b0)
    );

// If n63 is 0 and n62 is 1, Len_int must be 0 and Ren_int must be 1.
    check_len_zero_ren_one_when_n63_zero_n62_one: assert property (
        @(posedge clk) (n63 == 1'b0 && n62 == 1'b1) |-> (Len_int == 1'b0 && Ren_int == 1'b1)
    );

endmodule
