module hex_7_segment_sva (
    input logic [15:0] x,
    input logic        clk,
    input logic        clr,
    input logic [6:0]  a_to_g,
    input logic [3:0]  an,
    input logic [18:0] clkdiv
);

    function automatic logic [6:0] seg_map(input logic [3:0] d);
        begin
            case (d)
                4'h0: seg_map = 7'b0000001;
                4'h1: seg_map = 7'b1001111;
                4'h2: seg_map = 7'b0010010;
                4'h3: seg_map = 7'b0000110;
                4'h4: seg_map = 7'b1001100;
                4'h5: seg_map = 7'b0100100;
                4'h6: seg_map = 7'b0100000;
                4'h7: seg_map = 7'b0001111;
                4'h8: seg_map = 7'b0000000;
                4'h9: seg_map = 7'b0000100;
                4'hA: seg_map = 7'b0001000;
                4'hB: seg_map = 7'b1100000;
                4'hC: seg_map = 7'b0110001;
                4'hD: seg_map = 7'b1000010;
                4'hE: seg_map = 7'b0110000;
                4'hF: seg_map = 7'b0111000;
                default: seg_map = 7'b0000001;
            endcase
        end
    endfunction

    // Clear drives the divider to zero by the next sampled clock.
    check_clkdiv_clears_to_zero: assert property (
        @(posedge clk) clr |=> (clkdiv == 19'd0)
    );

    // Between sampled clocks, the divider either increments or is asynchronously cleared.
    check_clkdiv_progress_or_clear: assert property (
        @(posedge clk) disable iff (clr || $initstate)
        !$past(clr) |-> ((clkdiv == ($past(clkdiv) + 19'd1)) || (clkdiv == 19'd0))
    );

    // The active anode is selected by the top two divider bits.
    check_an_tracks_clkdiv: assert property (
        @(posedge clk) disable iff (clr)
        an == (4'b0001 << clkdiv[18:17])
    );

    // Exactly one anode is active.
    check_an_onehot: assert property (
        @(posedge clk) disable iff (clr)
        an inside {4'b0001, 4'b0010, 4'b0100, 4'b1000}
    );

    // an[0] selects the low nibble of x.
    check_display_nibble0: assert property (
        @(posedge clk) disable iff (clr)
        (an == 4'b0001) |-> (a_to_g == seg_map(x[3:0]))
    );

    // an[1] selects bits [7:4] of x.
    check_display_nibble1: assert property (
        @(posedge clk) disable iff (clr)
        (an == 4'b0010) |-> (a_to_g == seg_map(x[7:4]))
    );

    // an[2] selects bits [11:8] of x.
    check_display_nibble2: assert property (
        @(posedge clk) disable iff (clr)
        (an == 4'b0100) |-> (a_to_g == seg_map(x[11:8]))
    );

    // an[3] selects bits [15:12] of x.
    check_display_nibble3: assert property (
        @(posedge clk) disable iff (clr)
        (an == 4'b1000) |-> (a_to_g == seg_map(x[15:12]))
    );

    // After clear, the first digit is selected and shows the low nibble.
    check_reset_outputs_low_nibble: assert property (
        @(posedge clk) clr |=> ((an == 4'b0001) && (a_to_g == seg_map(x[3:0])))
    );

endmodule