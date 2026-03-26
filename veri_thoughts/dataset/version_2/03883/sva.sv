module counter_mux_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic       control,
    input logic       select,
    input logic [7:0] data_in,
    input logic [7:0] q,
    input logic [3:0] counter
);

    // Counter is forced to zero whenever reset is asserted low.
    check_counter_zero_while_reset_low: assert property (
        @(posedge clk) !reset |-> (counter == 4'd0)
    );

    // Enabled counter increments by one on the next clock.
    check_counter_increments_on_enable: assert property (
        @(posedge clk) disable iff (!reset)
        enable |=> (counter == ($past(counter) + 4'd1))
    );

    // Disabled counter holds its value on the next clock.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        !enable |=> (counter == $past(counter))
    );

    // Counter wraps from 4'hF to 4'h0 when enabled.
    check_counter_wraps_after_max: assert property (
        @(posedge clk) disable iff (!reset)
        (enable && (counter == 4'hF)) |=> (counter == 4'h0)
    );

    // Select high makes q follow data_in.
    check_q_selects_data_in: assert property (
        @(posedge clk) disable iff (!reset)
        select |-> (q == data_in)
    );

    // Select low and control high make q drive 8'hFF.
    check_q_selects_ff_on_control: assert property (
        @(posedge clk) disable iff (!reset)
        (!select && control) |-> (q == 8'hFF)
    );

    // Select low and control low make q drive the zero-extended counter.
    check_q_selects_counter_on_control_low: assert property (
        @(posedge clk) disable iff (!reset)
        (!select && !control) |-> (q == {4'h0, counter})
    );

    // During reset, the counter path drives zero on q.
    check_q_counter_path_zero_during_reset: assert property (
        @(posedge clk) (!reset && !select && !control) |-> (q == 8'h00)
    );

endmodule