// SVA checker for ycbcr_to_rgb
module ycbcr_to_rgb_sva (
    input logic                   clk,
    input logic [7:0]             y, cb, cr,
    input logic [7:0]             red, green, blue,

    // tap DUT internals for precise stage-by-stage checks
    input logic signed [8:0]      adj_y, adj_cb, adj_cr,
    input logic signed [17:0]     product_a, product_b, product_c, product_d, product_e,
    input logic signed [17:0]     sum_red, sum_green, sum_blue,
    input logic signed [8:0]      const0, const1, const2, const3, const4
);

    // Expected coefficients (from DUT)
    localparam logic signed [8:0] C0 = 9'sd128;
    localparam logic signed [8:0] C1 = 9'sd179;
    localparam logic signed [8:0] C2 = -9'sd91;
    localparam logic signed [8:0] C3 = -9'sd44;
    localparam logic signed [8:0] C4 = 9'sd227;

    // Past-valid enables for pipelined checks
    logic past1, past2, past3;
    always_ff @(posedge clk) begin
        past1 <= 1'b1;
        past2 <= past1;
        past3 <= past2;
    end

    // Helper: saturation identical to DUT
    function automatic logic [7:0] sat18_to_u8 (input logic signed [17:0] s);
        if (s[17])              return 8'h00;
        else if (s[16:15]==2'b11) return 8'hff;
        else                    return s[14:7];
    endfunction

    // Helpers: end-to-end expected 18-bit sums from raw inputs
    function automatic logic signed [17:0] sum_r_f(input logic [7:0] y_i, input logic [7:0] cr_i);
        return C0*$signed({1'b0,y_i}) + C1*($signed({1'b0,cr_i}) - 9'sd128);
    endfunction
    function automatic logic signed [17:0] sum_g_f(input logic [7:0] y_i, input logic [7:0] cb_i, input logic [7:0] cr_i);
        return C0*$signed({1'b0,y_i}) + C2*($signed({1'b0,cr_i}) - 9'sd128) + C3*($signed({1'b0,cb_i}) - 9'sd128);
    endfunction
    function automatic logic signed [17:0] sum_b_f(input logic [7:0] y_i, input logic [7:0] cb_i);
        return C0*$signed({1'b0,y_i}) + C4*($signed({1'b0,cb_i}) - 9'sd128);
    endfunction

    // Constant coefficients check
    assert property (@(posedge clk)
        const0==C0 && const1==C1 && const2==C2 && const3==C3 && const4==C4
    ) else $error("ycbcr_to_rgb: constant mismatch");

    // Stage 0: input adjust
    assert property (@(posedge clk) past1 |->
        adj_y == $past({1'b0,y}) &&
        adj_cr == ($past($signed({1'b0,cr})) - 9'sd128) &&
        adj_cb == ($past($signed({1'b0,cb})) - 9'sd128)
    ) else $error("ycbcr_to_rgb: adjust stage mismatch");

    // Stage 1: products
    assert property (@(posedge clk) past1 |->
        product_a == $past(const0*adj_y) &&
        product_b == $past(const1*adj_cr) &&
        product_c == $past(const2*adj_cr) &&
        product_d == $past(const3*adj_cb) &&
        product_e == $past(const4*adj_cb)
    ) else $error("ycbcr_to_rgb: product stage mismatch");

    // Stage 2: sums
    assert property (@(posedge clk) past2 |->
        sum_red   == $past(product_a + product_b) &&
        sum_green == $past(product_a + product_c + product_d) &&
        sum_blue  == $past(product_a + product_e)
    ) else $error("ycbcr_to_rgb: sum stage mismatch");

    // Stage 3: per-channel saturation/output
    assert property (@(posedge clk) past3 |-> red   == sat18_to_u8($past(sum_red ))) else $error("ycbcr_to_rgb: red saturation mismatch");
    assert property (@(posedge clk) past3 |-> green == sat18_to_u8($past(sum_green))) else $error("ycbcr_to_rgb: green saturation mismatch");
    assert property (@(posedge clk) past3 |-> blue  == sat18_to_u8($past(sum_blue ))) else $error("ycbcr_to_rgb: blue saturation mismatch");

    // End-to-end: 3-cycle latency from inputs to outputs
    assert property (@(posedge clk) past3 |->
        red   == sat18_to_u8( sum_r_f($past(y,3),             $past(cr,3)) ) &&
        green == sat18_to_u8( sum_g_f($past(y,3), $past(cb,3), $past(cr,3)) ) &&
        blue  == sat18_to_u8( sum_b_f($past(y,3), $past(cb,3)) )
    ) else $error("ycbcr_to_rgb: end-to-end mismatch");

    // No-X on outputs when inputs (3 cycles earlier) are known
    assert property (@(posedge clk)
        past3 && !$isunknown($past({y,cb,cr},3)) |-> !$isunknown({red,green,blue})
    ) else $error("ycbcr_to_rgb: X on outputs");

    // Coverage: exercise all saturation modes on all channels
    cover property (@(posedge clk) past3 && $past(sum_red)[17]                         && red   == 8'h00);
    cover property (@(posedge clk) past3 && !$past(sum_red)[17] && $past(sum_red)[16:15]==2'b11 && red   == 8'hff);
    cover property (@(posedge clk) past3 && !$past(sum_red)[17] && $past(sum_red)[16:15]!=2'b11 && red  != 8'h00 && red  != 8'hff);

    cover property (@(posedge clk) past3 && $past(sum_green)[17]                         && green == 8'h00);
    cover property (@(posedge clk) past3 && !$past(sum_green)[17] && $past(sum_green)[16:15]==2'b11 && green == 8'hff);
    cover property (@(posedge clk) past3 && !$past(sum_green)[17] && $past(sum_green)[16:15]!=2'b11 && green!= 8'h00 && green!= 8'hff);

    cover property (@(posedge clk) past3 && $past(sum_blue)[17]                         && blue  == 8'h00);
    cover property (@(posedge clk) past3 && !$past(sum_blue)[17] && $past(sum_blue)[16:15]==2'b11 && blue  == 8'hff);
    cover property (@(posedge clk) past3 && !$past(sum_blue)[17] && $past(sum_blue)[16:15]!=2'b11 && blue != 8'h00 && blue != 8'hff);

    // Coverage: both signs of chroma offsets seen
    cover property (@(posedge clk) past1 && adj_cr[8]==1'b0);
    cover property (@(posedge clk) past1 && adj_cr[8]==1'b1);
    cover property (@(posedge clk) past1 && adj_cb[8]==1'b0);
    cover property (@(posedge clk) past1 && adj_cb[8]==1'b1);

endmodule

// Bind example (place in a testbench or a separate bind file)
// Connect internal signals by name for full checking/coverage.
bind ycbcr_to_rgb ycbcr_to_rgb_sva u_ycbcr_to_rgb_sva (
    .clk      (clk),
    .y        (y),
    .cb       (cb),
    .cr       (cr),
    .red      (red),
    .green    (green),
    .blue     (blue),
    .adj_y    (adj_y),
    .adj_cb   (adj_cb),
    .adj_cr   (adj_cr),
    .product_a(product_a),
    .product_b(product_b),
    .product_c(product_c),
    .product_d(product_d),
    .product_e(product_e),
    .sum_red  (sum_red),
    .sum_green(sum_green),
    .sum_blue (sum_blue),
    .const0   (const0),
    .const1   (const1),
    .const2   (const2),
    .const3   (const3),
    .const4   (const4)
);