module mult_gate_sva (
    input logic clk,
    input logic Y,
    input logic J,
    input logic I,
    input logic H,
    input logic G,
    input logic F,
    input logic E,
    input logic D,
    input logic C,
    input logic B,
    input logic A
);

    // Y must equal J OR the three 3-input AND terms.
    check_output_equation: assert property (
        @(posedge clk)
        Y == (J | (I & H & G) | (F & E & D) | (C & B & A))
    );

    // J asserted must drive Y high.
    check_j_drives_y_high: assert property (
        @(posedge clk)
        J |-> Y
    );

    // I, H, and G all high must drive Y high.
    check_ihg_drives_y_high: assert property (
        @(posedge clk)
        (I & H & G) |-> Y
    );

    // F, E, and D all high must drive Y high.
    check_fed_drives_y_high: assert property (
        @(posedge clk)
        (F & E & D) |-> Y
    );

    // C, B, and A all high must drive Y high.
    check_cba_drives_y_high: assert property (
        @(posedge clk)
        (C & B & A) |-> Y
    );

    // Y high must come from J or one of the AND terms.
    check_y_high_has_valid_source: assert property (
        @(posedge clk)
        Y |-> (J | (I & H & G) | (F & E & D) | (C & B & A))
    );

    // With all source terms low, Y must be low.
    check_no_source_means_y_low: assert property (
        @(posedge clk)
        !(J | (I & H & G) | (F & E & D) | (C & B & A)) |-> !Y
    );

endmodule