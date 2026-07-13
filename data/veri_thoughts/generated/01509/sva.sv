module macc_simple_arst_clr_ena_sva (
    input logic        clk,
    input logic        rst,
    input logic        clr,
    input logic        ena,
    input logic [ 7:0] A,
    input logic [ 7:0] B,
    input logic [15:0] Z
);
    // While reset is asserted at a clock edge, Z must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (Z == 16'd0)
    );

    // When disabled in the previous cycle (and not in reset), Z holds its value.
    z_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && !ena) |-> (Z == $past(Z))
    );

    // With enable and clear in the previous cycle, Z loads A*B (no accumulation).
    z_loads_product_on_clr: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && ena && clr) |-> (Z == ($past(A) * $past(B)))
    );

    // With enable and no clear in the previous cycle, Z accumulates Z + A*B (truncated to 16 bits).
    z_accumulates_when_enabled: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && ena && !clr) |-> (Z == (($past(Z) + ($past(A) * $past(B))) & 16'hFFFF))
    );

    // When enabled in the previous cycle, Z follows either load or accumulate behavior based on clr.
    z_enabled_update_behavior: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && ena) |-> (
                Z == ( $past(clr)
                       ? ($past(A) * $past(B))
                       : (($past(Z) + ($past(A) * $past(B))) & 16'hFFFF) )
            )
    );

    // If enabled without clear and product is zero in the previous cycle, Z must hold.
    z_stable_when_addend_zero: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && ena && !clr && (($past(A) * $past(B)) == 16'd0)) |-> (Z == $past(Z))
    );
endmodule