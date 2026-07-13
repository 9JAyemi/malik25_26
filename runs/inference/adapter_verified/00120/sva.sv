module sky130_fd_sc_ms__a2111oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// Y matches the RTL sum-of-products equation.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == ((A1 & A2 & B1 & C1 & D1) |
              (A1 & A2 & ~B1 & C1 & D1) |
              (A1 & A2 & B1 & ~C1 & D1) |
              (A1 & A2 & B1 & C1 & ~D1) |
              (~A1 & ~A2 & B1 & C1 & D1) |
              (~A1 & ~A2 & ~B1 & C1 & D1) |
              (~A1 & ~A2 & B1 & ~C1 & D1) |
              (~A1 & ~A2 & B1 & C1 & ~D1) |
              (~A1 & A2 & B1 & C1 & D1) |
              (~A1 & A2 & ~B1 & C1 & D1) |
              (~A1 & A2 & B1 & ~C1 & D1) |
              (~A1 & A2 & B1 & C1 & ~D1) |
              (A1 & ~A2 & B1 & C1 & D1) |
              (A1 & ~A2 & ~B1 & C1 & D1) |
              (A1 & ~A2 & B1 & ~C1 & D1) |
              (A1 & ~A2 & B1 & C1 & ~D1))
    );

// All asserted inputs drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk)
        (A1 & A2 & B1 & C1 & D1) |-> Y
    );

// Any two asserted inputs with B1, C1, and D1 high drive Y high.
    check_two_inputs_with_bcd_high_drive_y_high: assert property (
        @(posedge clk)
        ((A1 & A2 & B1 & C1 & ~D1) |
         (A1 & A2 & B1 & ~C1 & D1) |
         (A1 & A2 & ~B1 & C1 & D1)) |-> Y
    );

// Any two asserted inputs with A1, A2, and D1 high drive Y high.
    check_two_inputs_with_a2d_high_drive_y_high: assert property (
        @(posedge clk)
        ((A1 & A2 & ~B1 & C1 & D1) |
         (A1 & A2 & B1 & ~C1 & D1) |
         (A1 & A2 & B1 & C1 & ~D1)) |-> Y
    );

// Any two asserted inputs with A1, A2, and C1 high drive Y high.
    check_two_inputs_with_a2c_high_drive_y_high: assert property (
        @(posedge clk)
        ((A1 & A2 & ~B1 & ~C1 & D1) |
         (A1 & A2 & B1 & ~C1 & D1) |
         (A1 & A2 & B1 & C1 & ~D1)) |-> Y
    );

// Any two asserted inputs with A1, B1, and D1 high drive Y high.
    check_two_inputs_with_abd_high_drive_y_high: assert property (
        @(posedge clk)
        ((A1 & ~A2 & B1 & C1 & D1) |
         (A1 & ~A2 & ~B1 & C1 & D1) |
         (A1 & ~A2 & B1 & ~C1 & D1)) |-> Y
    );

// Any two asserted inputs with A1, B1, and C1 high drive Y high.
    check_two_inputs_with_abc_high_drive_y_high: assert property (
        @(posedge clk)
        ((A1 & ~A2 & ~B1 & C1 & D1) |
         (A1 & ~A2 & B1 & ~C1 & D1) |
         (A1 & ~A2 & B1 & C1 & ~D1)) |-> Y
    );

// Any two asserted inputs with A2, C1, and D1 high drive Y high.
    check_two_inputs_with_acd_high_drive_y_high: assert property (
        @(posedge clk)
        ((~A1 & A2 & C1 & D1 & ~B1) |
         (~A1 & A2 & ~C1 & D1 & B1) |
         (~A1 & A2 & C1 & ~D1 & B1)) |-> Y
    );

// Any two asserted inputs with A2, B1, and D1 high drive Y high.
    check_two_inputs_with_abd_high_drive_y_high_2: assert property (
        @(posedge clk)
        ((~A1 & A2 & ~C1 & D1 & B1) |
         (~A1 & A2 & C1 & ~D1 & B1) |
         (~A1 & A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A2, B1, and C1 high drive Y high.
    check_two_inputs_with_abc_high_drive_y_high_2: assert property (
        @(posedge clk)
        ((~A1 & A2 & ~C1 & ~D1 & B1) |
         (~A1 & A2 & C1 & ~D1 & B1) |
         (~A1 & A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A1, C1, and D1 high drive Y high.
    check_two_inputs_with_acd_high_drive_y_high_3: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & C1 & D1 & B1) |
         (~A1 & ~A2 & ~C1 & D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1)) |-> Y
    );

// Any two asserted inputs with A1, B1, and D1 high drive Y high.
    check_two_inputs_with_abd_high_drive_y_high_3: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & ~C1 & D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A1, B1, and C1 high drive Y high.
    check_two_inputs_with_abc_high_drive_y_high_3: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & ~C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A2, C1, and D1 high drive Y high.
    check_two_inputs_with_acd_high_drive_y_high_4: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & C1 & D1 & ~B1) |
         (~A1 & ~A2 & ~C1 & D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1)) |-> Y
    );

// Any two asserted inputs with A2, B1, and D1 high drive Y high.
    check_two_inputs_with_abd_high_drive_y_high_4: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & ~C1 & D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A2, B1, and C1 high drive Y high.
    check_two_inputs_with_abc_high_drive_y_high_4: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & ~C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & ~D1 & B1) |
         (~A1 & ~A2 & C1 & D1 & ~B1)) |-> Y
    );

// Any two asserted inputs with A1, C1, and D1 high drive Y high.
    check_two_inputs_with_acd_high_drive_y_high_5: assert property (
        @(posedge clk)
        ((~A1 & ~A2 & C1 & D1 & ~B1) |
         (~A1 & ~A2 & ~C1 & D1 & B1