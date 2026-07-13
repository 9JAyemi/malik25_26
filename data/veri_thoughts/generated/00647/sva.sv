module pipestage_sva
  #(parameter TAGWIDTH = 1)
   (input  logic                 clk,
    input  logic                 reset,     // active-HIGH synchronous reset
    input  logic                 stb_in,
    input  logic                 stb_out,
    input  logic                 valid,
    input  logic [TAGWIDTH-1:0]  tag_in,
    input  logic [TAGWIDTH-1:0]  tag_out);

    // Synchronous reset drives valid/tag_out to zero by next cycle.
    check_sync_reset_clears_next: assert property (
        @(posedge clk) reset |=> (valid == 1'b0) && (tag_out == '0)
    );

    // On stb_in, next-cycle valid=1 and tag_out captures tag_in from prior cycle.
    check_load_on_stb_in: assert property (
        @(posedge clk) disable iff (reset) stb_in |=> (valid == 1'b1) && (tag_out == $past(tag_in))
    );

    // On stb_out without stb_in, next-cycle valid=0 and tag_out=0.
    check_clear_on_stb_out: assert property (
        @(posedge clk) disable iff (reset) (stb_out && !stb_in) |=> (valid == 1'b0) && (tag_out == '0)
    );

    // If both stb_in and stb_out, stb_in has priority (load occurs).
    check_priority_in_over_out: assert property (
        @(posedge clk) disable iff (reset) (stb_in && stb_out) |=> (valid == 1'b1) && (tag_out == $past(tag_in))
    );

    // When no strobes, registers hold their previous values.
    check_hold_on_idle: assert property (
        @(posedge clk) disable iff (reset) (!stb_in && !stb_out) |=> (valid == $past(valid)) && (tag_out == $past(tag_out))
    );

    // valid can only rise due to stb_in in the previous cycle.
    check_valid_rise_cause: assert property (
        @(posedge clk) disable iff (reset) $rose(valid) |-> $past(stb_in)
    );

    // valid can only fall due to stb_out (with no stb_in) in the previous cycle.
    check_valid_fall_cause: assert property (
        @(posedge clk) disable iff (reset) $fell(valid) |-> $past(stb_out && !stb_in)
    );

    // After stb_in, if next cycle is idle, loaded tag/value persist.
    check_persist_after_load_when_idle: assert property (
        @(posedge clk) disable iff (reset)
            (stb_in) |=> (!stb_in && !stb_out) |-> (valid == 1'b1) && (tag_out == $past(tag_in,1))
    );

    // After stb_out (without stb_in), if next cycle is idle, cleared state persists.
    check_persist_after_clear_when_idle: assert property (
        @(posedge clk) disable iff (reset)
            (stb_out && !stb_in) |=> (!stb_in && !stb_out) |-> (valid == 1'b0) && (tag_out == '0)
    );

endmodule