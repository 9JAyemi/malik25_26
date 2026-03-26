module ym_sync_sva(
    input logic rst,
    input logic clk,
    input logic ym_p1,
    input logic ym_so,
    input logic ym_sh1,
    input logic ym_sh2,
    input logic ym_irq_n,
    input logic [7:0] ym_data,
    input logic ym_p1_sync,
    input logic ym_so_sync,
    input logic ym_sh1_sync,
    input logic ym_sh2_sync,
    input logic ym_irq_n_sync,
    input logic [7:0] ym_data_sync,
    input logic p1_0,
    input logic so_0,
    input logic sh1_0,
    input logic sh2_0,
    input logic irq_0,
    input logic [7:0] data0
);

    // First stage is clocked by ym_p1; second stage is clocked by clk.
    // rst is an active-high asynchronous reset for both stages.

    property first_stage_capture_p;
        logic p1_s, so_s, sh1_s, sh2_s, irq_s;
        logic [7:0] data_s;
        @(posedge ym_p1) disable iff (rst)
            (1'b1,
             p1_s = ym_p1,
             so_s = ym_so,
             sh1_s = ym_sh1,
             sh2_s = ym_sh2,
             irq_s = ym_irq_n,
             data_s = ym_data)
            |=> (p1_0 == p1_s &&
                 so_0 == so_s &&
                 sh1_0 == sh1_s &&
                 sh2_0 == sh2_s &&
                 irq_0 == irq_s &&
                 data0 == data_s);
    endproperty

    property second_stage_capture_p;
        logic p1_s, so_s, sh1_s, sh2_s, irq_s;
        logic [7:0] data_s;
        @(posedge clk) disable iff (rst)
            (1'b1,
             p1_s = p1_0,
             so_s = so_0,
             sh1_s = sh1_0,
             sh2_s = sh2_0,
             irq_s = irq_0,
             data_s = data0)
            |=> (ym_p1_sync == p1_s &&
                 ym_so_sync == so_s &&
                 ym_sh1_sync == sh1_s &&
                 ym_sh2_sync == sh2_s &&
                 ym_irq_n_sync == irq_s &&
                 ym_data_sync == data_s);
    endproperty

    property first_stage_reset_p;
        @(posedge ym_p1)
            rst |=> (p1_0 == 1'b0 &&
                     so_0 == 1'b0 &&
                     sh1_0 == 1'b0 &&
                     sh2_0 == 1'b0 &&
                     irq_0 == 1'b1 &&
                     data0 == 8'h00);
    endproperty

    property second_stage_reset_p;
        @(posedge clk)
            rst |=> (ym_p1_sync == 1'b0 &&
                     ym_so_sync == 1'b0 &&
                     ym_sh1_sync == 1'b0 &&
                     ym_sh2_sync == 1'b0 &&
                     ym_irq_n_sync == 1'b1 &&
                     ym_data_sync == 8'h00);
    endproperty

    // First stage captures YM inputs on each ym_p1 edge.
    check_first_stage_capture: assert property (first_stage_capture_p);

    // Second stage captures the first-stage registers on each clk edge.
    check_second_stage_capture: assert property (second_stage_capture_p);

    // A reset seen on ym_p1 leaves the first-stage registers at their reset values.
    check_first_stage_reset: assert property (first_stage_reset_p);

    // A reset seen on clk leaves the synchronized outputs at their reset values.
    check_second_stage_reset: assert property (second_stage_reset_p);

endmodule