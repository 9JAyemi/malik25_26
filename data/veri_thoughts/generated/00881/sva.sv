module reconocedor_cursor_sva (
    input logic clk,                 // SVA clock (DUT is combinational)
    input logic [2:0] visor_x,
    input logic [1:0] visor_y,
    input logic [7:0] valor,
    input logic is_number
);

    ///// Number region (x in 0..3) /////
    // For x<=3, is_number must be 1.
    check_is_number_when_x_le_3: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x <= 3'd3) |-> (is_number == 1'b1)
    );

    // For x>3, is_number must be 0.
    check_not_number_when_x_gt_3: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x > 3'd3) |-> (is_number == 1'b0)
    );

    // For x<=3, upper nibble of valor must be zero (0..15).
    check_number_val_upper_zero: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x <= 3'd3) |-> (valor[7:4] == 4'h0)
    );

    // For x<=3, lower nibble encodes {visor_y, visor_x[1:0]} (y*4 + x).
    check_number_val_lower_nibble: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x <= 3'd3) |-> (valor[3:0] == {visor_y, visor_x[1:0]})
    );

    ///// Non-number explicit mappings for x=4,5 and y=0..2 /////
    // x=4,y=0 -> 16, non-number.
    check_x4_y0: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd4 && visor_y==2'd0) |-> (valor==8'd16 && is_number==1'b0)
    );

    // x=5,y=0 -> 17, non-number.
    check_x5_y0: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd5 && visor_y==2'd0) |-> (valor==8'd17 && is_number==1'b0)
    );

    // x=4,y=1 -> 18, non-number.
    check_x4_y1: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd4 && visor_y==2'd1) |-> (valor==8'd18 && is_number==1'b0)
    );

    // x=5,y=1 -> 19, non-number.
    check_x5_y1: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd5 && visor_y==2'd1) |-> (valor==8'd19 && is_number==1'b0)
    );

    // x=4,y=2 -> 20, non-number.
    check_x4_y2: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd4 && visor_y==2'd2) |-> (valor==8'd20 && is_number==1'b0)
    );

    // x=5,y=2 -> 21, non-number.
    check_x5_y2: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd5 && visor_y==2'd2) |-> (valor==8'd21 && is_number==1'b0)
    );

    ///// Edge rows and defaults /////
    // x=4,y=3 -> 22, non-number.
    check_x4_y3: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd4 && visor_y==2'd3) |-> (valor==8'd22 && is_number==1'b0)
    );

    // x=5,y=3 -> default 28, non-number.
    check_x5_y3_default: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x==3'd5 && visor_y==2'd3) |-> (valor==8'd28 && is_number==1'b0)
    );

    // For x>=6, default 28, non-number (all y).
    check_x_ge_6_default: assert property (
        @(posedge clk) disable iff (1'b0) (visor_x >= 3'd6) |-> (valor==8'd28 && is_number==1'b0)
    );

endmodule