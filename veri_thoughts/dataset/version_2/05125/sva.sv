module pipestage_sva
  #(parameter TAGWIDTH = 1)
   (input logic clk,
    input logic reset,
    input logic stb_in,
    input logic stb_out,
    input logic valid,
    input logic [TAGWIDTH-1:0] tag_in,
    input logic [TAGWIDTH-1:0] tag_out);

    // Reset clears valid.
    check_reset_clears_valid: assert property (
        @(posedge clk) reset |=> (valid == 1'b0)
    );

    // Reset clears tag_out.
    check_reset_clears_tag: assert property (
        @(posedge clk) reset |=> (tag_out == '0)
    );

    // stb_in sets valid on the next cycle.
    check_load_sets_valid: assert property (
        @(posedge clk) disable iff (reset) stb_in |=> (valid == 1'b1)
    );

    // stb_in captures tag_in on the next cycle.
    check_load_captures_tag: assert property (
        @(posedge clk) disable iff (reset) stb_in |=> (tag_out == $past(tag_in))
    );

    // stb_out clears valid when no load is requested.
    check_clear_clears_valid: assert property (
        @(posedge clk) disable iff (reset) (!stb_in && stb_out) |=> (valid == 1'b0)
    );

    // stb_out clears tag_out when no load is requested.
    check_clear_clears_tag: assert property (
        @(posedge clk) disable iff (reset) (!stb_in && stb_out) |=> (tag_out == '0)
    );

    // With no strobes, valid holds its value.
    check_idle_holds_valid: assert property (
        @(posedge clk) disable iff (reset) (!stb_in && !stb_out) |=> $stable(valid)
    );

    // With no strobes, tag_out holds its value.
    check_idle_holds_tag: assert property (
        @(posedge clk) disable iff (reset) (!stb_in && !stb_out) |=> $stable(tag_out)
    );

    // stb_in has priority over stb_out for valid.
    check_stb_in_priority_valid: assert property (
        @(posedge clk) disable iff (reset) (stb_in && stb_out) |=> (valid == 1'b1)
    );

    // stb_in has priority over stb_out for tag capture.
    check_stb_in_priority_tag: assert property (
        @(posedge clk) disable iff (reset) (stb_in && stb_out) |=> (tag_out == $past(tag_in))
    );

endmodule