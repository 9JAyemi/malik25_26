module up_down_counter_4bit_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic en,
    input logic [3:0] data_in,
    input logic [3:0] out
);

    // If en was 0 last cycle, out holds its value.
    hold_when_en_low: assert property (
        @(posedge clk) ($past(en) == 1'b0) |-> (out == $past(out))
    );

    // If en and load were 1 last cycle, out captures data_in.
    load_captures_data: assert property (
        @(posedge clk) ($past(en) && $past(load)) |-> (out == $past(data_in))
    );

    // If en=1, load=0, up_down=1 last cycle, out increments by 1 (mod 16).
    count_up_next_value: assert property (
        @(posedge clk) ($past(en) && !$past(load) && $past(up_down)) |-> (out == ($past(out) + 4'd1))
    );

    // If en=1, load=0, up_down=0 last cycle, out decrements by 1 (mod 16).
    count_down_next_value: assert property (
        @(posedge clk) ($past(en) && !$past(load) && !$past(up_down)) |-> (out == ($past(out) - 4'd1))
    );

    // When enabled last cycle, next out equals load data or +/-1 as selected.
    functional_update_when_enabled: assert property (
        @(posedge clk) $past(en) |-> (
            out == ( $past(load)
                     ? $past(data_in)
                     : ( $past(up_down) ? ($past(out) + 4'd1) : ($past(out) - 4'd1) )
                   )
        )
    );

    // Any change in out implies en was 1 in the prior cycle.
    change_implies_enabled: assert property (
        @(posedge clk) (out != $past(out)) |-> $past(en)
    );

    // When counting (enabled, no load), out always changes from prior value.
    counting_changes_value: assert property (
        @(posedge clk) ($past(en) && !$past(load)) |-> (out != $past(out))
    );

    // If out did not change, reason is en=0 or a load of the same value.
    stable_out_has_reason: assert property (
        @(posedge clk) (out == $past(out)) |-> (
            ($past(en) == 1'b0) ||
            ($past(en) && $past(load) && ($past(data_in) == $past(out)))
        )
    );

    // Count up from 4'hF wraps to 4'h0.
    wrap_on_increment_from_max: assert property (
        @(posedge clk) ($past(en) && !$past(load) && $past(up_down) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

    // Count down from 4'h0 wraps to 4'hF.
    wrap_on_decrement_from_min: assert property (
        @(posedge clk) ($past(en) && !$past(load) && !$past(up_down) && ($past(out) == 4'h0)) |-> (out == 4'hF)
    );

endmodule