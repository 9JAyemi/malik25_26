module jt51_sh1_sva #(
    parameter stages = 32
) (
    input logic              clk,
    input logic              en,
    input logic              ld,
    input logic              din,
    input logic              drop,
    input logic [stages-1:0] shift,
    input logic              next
);

    // next selects din when ld is asserted.
    check_next_from_din_when_load: assert property (
        @(posedge clk) ld |-> (next === din)
    );

    // next recirculates drop when ld is deasserted.
    check_next_from_drop_when_shift: assert property (
        @(posedge clk) !ld |-> (next === drop)
    );

    // drop is always driven from the shift register LSB.
    check_drop_matches_shift_lsb: assert property (
        @(posedge clk) drop === shift[0]
    );

    property p_shift_holds_when_disabled;
        logic [stages-1:0] prev_shift;
        @(posedge clk) (!en, prev_shift = shift) |=> (shift === prev_shift);
    endproperty
    // shift holds its state when en is low.
    check_shift_holds_when_disabled: assert property (p_shift_holds_when_disabled);

    property p_drop_holds_when_disabled;
        logic prev_drop;
        @(posedge clk) (!en, prev_drop = drop) |=> (drop === prev_drop);
    endproperty
    // drop holds its value when en is low.
    check_drop_holds_when_disabled: assert property (p_drop_holds_when_disabled);

    property p_load_captures_din_to_msb;
        logic prev_din;
        @(posedge clk) (en && ld, prev_din = din) |=> (shift[stages-1] === prev_din);
    endproperty
    // enabled load writes din into the MSB.
    check_load_captures_din_to_msb: assert property (p_load_captures_din_to_msb);

    property p_recirculate_captures_drop_to_msb;
        logic prev_drop;
        @(posedge clk) (en && !ld, prev_drop = drop) |=> (shift[stages-1] === prev_drop);
    endproperty
    // enabled shift without load recirculates drop into the MSB.
    check_recirculate_captures_drop_to_msb: assert property (p_recirculate_captures_drop_to_msb);

    generate
        if (stages > 1) begin : g_shift_checks
            genvar j;
            for (j = 0; j < stages-1; j = j + 1) begin : g_stage
                property p_shift_moves_down;
                    logic prev_bit;
                    @(posedge clk) (en, prev_bit = shift[j+1]) |=> (shift[j] === prev_bit);
                endproperty
                // enabled shift moves each bit down by one stage.
                check_shift_moves_down: assert property (p_shift_moves_down);
            end

            property p_enabled_drop_follows_stage1;
                logic prev_stage1;
                @(posedge clk) (en, prev_stage1 = shift[1]) |=> (drop === prev_stage1);
            endproperty
            // enabled shift updates drop from the next stage.
            check_enabled_drop_follows_stage1: assert property (p_enabled_drop_follows_stage1);
        end
    endgenerate

endmodule