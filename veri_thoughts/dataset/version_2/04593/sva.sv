module RGB_color_set_sva(
    input logic clk,
    input logic [1:0] button,
    input logic [23:0] RGBcolor,
    input logic [1:0] cunt,
    input logic [7:0] red,
    input logic [7:0] gre,
    input logic [7:0] blu
);

    // RGBcolor is always the concatenation of the three channel registers.
    check_rgbcolor_concat: assert property (
        @(posedge clk) RGBcolor === {red, gre, blu}
    );

    // The 2-bit color selector increments on each rising edge of button[0].
    check_selector_increments_on_button0: assert property (
        @(posedge button[0]) 1'b1 |=> (cunt == ($past(cunt) + 2'd1))
    );

    // button[1] has priority and selects the 0x5F gray value.
    check_button1_override_color: assert property (
        @(posedge clk) button[1] |=> (RGBcolor == 24'h5F5F5F)
    );

    // With button[1] low and selector 1, the next color is red.
    check_selector1_red: assert property (
        @(posedge clk) (!button[1] && (cunt == 2'd1)) |=> (RGBcolor == 24'h7F0000)
    );

    // With button[1] low and selector 2, the next color is green.
    check_selector2_green: assert property (
        @(posedge clk) (!button[1] && (cunt == 2'd2)) |=> (RGBcolor == 24'h007F00)
    );

    // With button[1] low and selector 3, the next color is blue.
    check_selector3_blue: assert property (
        @(posedge clk) (!button[1] && (cunt == 2'd3)) |=> (RGBcolor == 24'h00007F)
    );

    // With button[1] low and selector 0, the next color is the default gray.
    check_selector0_default_gray: assert property (
        @(posedge clk) (!button[1] && (cunt == 2'd0)) |=> (RGBcolor == 24'h3F3F3F)
    );

    // Each clk update produces one of the five implemented RGB encodings.
    check_rgbcolor_valid_encoding: assert property (
        @(posedge clk) 1'b1 |=> (
            (RGBcolor == 24'h5F5F5F) ||
            (RGBcolor == 24'h7F0000) ||
            (RGBcolor == 24'h007F00) ||
            (RGBcolor == 24'h00007F) ||
            (RGBcolor == 24'h3F3F3F)
        )
    );

endmodule