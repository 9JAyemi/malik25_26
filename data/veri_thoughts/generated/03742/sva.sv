module clk_div_sva (
    input logic        CLKIN,
    input logic        RST,
    input logic [3:0]  BAUD,
    input logic        CLKOUT,
    input logic [19:0] clk_cntr,
    input logic [19:0] baud_rate
);

    localparam logic [19:0] B300    = {1'b0, 19'b1010001011000010100};
    localparam logic [19:0] B600    = {1'b0, 19'b0101000101100001010};
    localparam logic [19:0] B1200   = {1'b0, 19'b0010100010110000100};
    localparam logic [19:0] B2400   = {1'b0, 19'b0001010001011000010};
    localparam logic [19:0] B4800   = {1'b0, 19'b0000101000101100000};
    localparam logic [19:0] B9600   = {1'b0, 19'b0000010100010110000};
    localparam logic [19:0] B19200  = {1'b0, 19'b0000001010001010111};
    localparam logic [19:0] B38400  = {1'b0, 19'b0000000101000101011};
    localparam logic [19:0] B57600  = {1'b0, 19'b0000000011011000111};
    localparam logic [19:0] B115200 = {1'b0, 19'b0000000001101100011};

    // Reset forces the default baud divisor.
    check_reset_forces_default_baud: assert property (
        @(posedge CLKIN) RST |-> (baud_rate == B9600)
    );

    // BAUD 0 selects the 300 divisor.
    check_baud_0_maps_to_b300: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h0) |-> (baud_rate == B300)
    );

    // BAUD 1 selects the 600 divisor.
    check_baud_1_maps_to_b600: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h1) |-> (baud_rate == B600)
    );

    // BAUD 2 selects the 1200 divisor.
    check_baud_2_maps_to_b1200: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h2) |-> (baud_rate == B1200)
    );

    // BAUD 3 selects the 2400 divisor.
    check_baud_3_maps_to_b2400: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h3) |-> (baud_rate == B2400)
    );

    // BAUD 4 selects the 4800 divisor.
    check_baud_4_maps_to_b4800: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h4) |-> (baud_rate == B4800)
    );

    // BAUD 5 selects the 9600 divisor.
    check_baud_5_maps_to_b9600: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h5) |-> (baud_rate == B9600)
    );

    // BAUD 6 selects the 19200 divisor.
    check_baud_6_maps_to_b19200: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h6) |-> (baud_rate == B19200)
    );

    // BAUD 7 selects the 38400 divisor.
    check_baud_7_maps_to_b38400: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h7) |-> (baud_rate == B38400)
    );

    // BAUD 8 selects the 57600 divisor.
    check_baud_8_maps_to_b57600: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h8) |-> (baud_rate == B57600)
    );

    // BAUD 9 selects the 115200 divisor.
    check_baud_9_maps_to_b115200: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD == 4'h9) |-> (baud_rate == B115200)
    );

    // Unsupported BAUD values fall back to the 9600 divisor.
    check_baud_default_maps_to_b9600: assert property (
        @(posedge CLKIN) disable iff (RST) (BAUD > 4'h9) |-> (baud_rate == B9600)
    );

    // A reset cycle clears the counter and output by the next clock.
    check_reset_clears_counter_and_output: assert property (
        @(posedge CLKIN) RST |=> ((clk_cntr == 20'd0) && (CLKOUT == 1'b0))
    );

    // When not at the divisor, the counter increments and output holds.
    check_counter_advances_and_output_holds: assert property (
        @(posedge CLKIN) disable iff (RST)
        (clk_cntr != baud_rate) |=> ((clk_cntr == ($past(clk_cntr) + 20'd1)) && (CLKOUT == $past(CLKOUT)))
    );

    // When the divisor is reached, the counter clears and output toggles.
    check_terminal_count_resets_and_toggles: assert property (
        @(posedge CLKIN) disable iff (RST)
        (clk_cntr == baud_rate) |=> ((clk_cntr == 20'd0) && (CLKOUT != $past(CLKOUT)))
    );

endmodule