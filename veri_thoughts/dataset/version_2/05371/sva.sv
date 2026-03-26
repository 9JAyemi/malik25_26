module delay_gate_sva (
    input logic       in,
    input logic       rst,
    input logic       en,
    input logic       clk,
    input logic       out,
    input logic [3:0] delay_reg,
    input logic [3:0] next_delay_reg
);

    // Clock: clk
    // Reset: rst, active-high synchronous
    // Logic: sequential delay_reg with combinational next_delay_reg and out

    // next_delay_reg is the shifted version of delay_reg with in loaded into bit 0.
    check_next_delay_reg_wiring: assert property (
        @(posedge clk) disable iff (rst)
        next_delay_reg == {delay_reg[2], delay_reg[1], delay_reg[0], in}
    );

    // out always reflects the most significant bit of delay_reg.
    check_out_matches_delay_reg_msb: assert property (
        @(posedge clk) disable iff (rst)
        out == delay_reg[3]
    );

    // A reset cycle leaves delay_reg cleared on the following cycle.
    check_delay_reg_zero_after_reset: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (delay_reg == 4'b0000)
    );

    // A reset cycle leaves out low on the following cycle.
    check_out_zero_after_reset: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (out == 1'b0)
    );

    // When enabled, delay_reg captures the previous next_delay_reg value.
    check_delay_reg_updates_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && $past(en)) |-> (delay_reg == $past(next_delay_reg))
    );

    // When disabled, delay_reg holds its previous value.
    check_delay_reg_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && !$past(en)) |-> (delay_reg == $past(delay_reg))
    );

    // When enabled, out advances from the previous stage-2 value.
    check_out_advances_on_enable: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && $past(en)) |-> (out == $past(delay_reg[2]))
    );

    // When disabled, out holds its previous value.
    check_out_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && !$past(en)) |-> (out == $past(out))
    );

    // Four consecutive enabled cycles delay in to out by four clocks.
    check_four_cycle_delay_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        ($past(!rst && en, 1) &&
         $past(!rst && en, 2) &&
         $past(!rst && en, 3) &&
         $past(!rst && en, 4)) |-> (out == $past(in, 4))
    );

endmodule

bind delay_gate delay_gate_sva delay_gate_sva_inst (
    .in(in),
    .rst(rst),
    .en(en),
    .clk(clk),
    .out(out),
    .delay_reg(delay_reg),
    .next_delay_reg(next_delay_reg)
);